/*
 * Copyright (c) 2018 Demerzel Solutions Limited
 * This file is part of the Nethermind library.
 *
 * The Nethermind library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The Nethermind library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the Nethermind. If not, see <http://www.gnu.org/licenses/>.
 */

using System;
using System.Collections;
using System.Collections.Generic;
using System.ComponentModel.Design;
using System.Numerics;
using System.Runtime.CompilerServices;
using Nethermind.Core;
using Nethermind.Core.Crypto;
using Nethermind.Core.Extensions;
using Nethermind.Core.Specs;
using Nethermind.Dirichlet.Numerics;
using Nethermind.Evm.Precompiles;
using Nethermind.Evm.Tracing;
using Nethermind.Logging;
using Nethermind.Store;

[assembly:InternalsVisibleTo("Nethermind.Evm.Test")]
namespace Nethermind.Evm
{
    public class VirtualMachine : IVirtualMachine
    {
        private const EvmExceptionType BadInstructionErrorText = EvmExceptionType.BadInstruction;
        private const EvmExceptionType OutOfGasErrorText = EvmExceptionType.OutOfGas;

        public const int MaxCallDepth = 1024;
        public const int MaxStackSize = 1025;

        private bool _simdOperationsEnabled = Vector<byte>.Count == 32;
        private BigInteger P255Int = BigInteger.Pow(2, 255);
        private BigInteger P256Int = BigInteger.Pow(2, 256);
        private BigInteger P255 => P255Int;
        private BigInteger BigInt256 = 256;
        public BigInteger BigInt32 = 32;

        internal byte[] BytesZero = {0};

        internal byte[] BytesZero32 =
        {
            0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0
        };

        internal byte[] BytesMax32 =
        {
            255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255
        };

        private byte[] _chainId;

        private readonly IBlockhashProvider _blockhashProvider;
        private readonly ISpecProvider _specProvider;
        private readonly LruCache<Keccak, CodeInfo> _codeCache = new LruCache<Keccak, CodeInfo>(4 * 1024);
        private readonly ILogger _logger;
        private readonly IStateProvider _state;
        private readonly Stack<EvmState> _stateStack = new Stack<EvmState>();
        private readonly IStorageProvider _storage;
        private Address _parityTouchBugAccount;
        private Dictionary<Address, IPrecompiledContract> _precompiles;
        private byte[] _returnDataBuffer = new byte[0];
        private ITxTracer _txTracer;

        public bool TraceDU { get; set; } = false;
        public bool IsDeployingTarget { get; set; } = false;
        public bool HadDeployerTx { get; set; } = false;
        public bool IsRedirected { get; set; } = false;

        public Address TargetContractAddr { get; set; } = Address.Zero;
        public Address TargetOwnerAddr { get; set; } = Address.Zero;
        private Address[] NormalUsers = new Address[32];
        private int NormalUserCount = 0;

        public Dictionary<UInt256, TaintInfo> taintStorage = new Dictionary<UInt256, TaintInfo>();
        public SortedSet<int> VisitedEdgeSet { get; set; } = new SortedSet<int>();
        public SortedSet<int> VisitedInstrs { get; set; } = new SortedSet<int>();
        // PC, Op, Oprnd1, Oprnd2
        public List<(int, string, BigInteger, BigInteger)> CmpList { get; set; } = new List<(int, string, BigInteger, BigInteger)>();
        public Dictionary<UInt256, int> DefPCMap { get; set; } = new Dictionary<UInt256, int>();
        public SortedSet<(int, int, UInt256)> DefUseChainSet { get; set; } = new SortedSet<(int, int, UInt256)>();
        public HashSet<(BugClass, int)> BugSet { get; set; } = new HashSet<(BugClass, int)>();
        public BugOracle BugOracle = new BugOracle();

        public VirtualMachine(IStateProvider stateProvider, IStorageProvider storageProvider,
            IBlockhashProvider blockhashProvider, ISpecProvider specProvider, ILogManager logManager)
        {
            _logger = logManager?.GetClassLogger() ?? throw new ArgumentNullException(nameof(logManager));
            _state = stateProvider ?? throw new ArgumentNullException(nameof(stateProvider));
            _storage = storageProvider ?? throw new ArgumentNullException(nameof(storageProvider));
            _blockhashProvider = blockhashProvider ?? throw new ArgumentNullException(nameof(blockhashProvider));
            _specProvider = specProvider ?? throw new ArgumentNullException(nameof(specProvider));
            _chainId = specProvider.ChainId.ToBigEndianByteArray();
            InitializePrecompiledContracts();
        }

        public void PostprocessBugs(ExecutionEnvironment env)
        {
            CheckBlockStateDependencySFuzz(env);
            CheckMishandledException();
            CheckReentrancySFuzz(env);
            CheckReentrancyILF();
        }

        private bool IsTargetContract(Address addr)
        {
            return (TargetContractAddr != Address.Zero && TargetContractAddr == addr);
        }

        private bool IsTargetOwner(Address addr)
        {
            return (TargetOwnerAddr != Address.Zero && TargetOwnerAddr == addr);
        }

        public void RegisterUser(Address addr)
        {
            if (NormalUserCount < 32)
            {
                NormalUsers[NormalUserCount++] = addr;
            }
        }

        private bool IsUser(Address addr)
        {
            int i;
            for (i = 0; i < NormalUserCount; i++)
            {
                if (NormalUsers[i] == addr)
                {
                    return true;
                }
            }
            return false;
        }

        private void CheckBlockStateDependencySFuzz(ExecutionEnvironment env)
        {
            // sFuzz checks whether there was any block state instruction and ether transfer.
            // Note that sFuzz also considers env.Value > 0 as ether transfer (maybe a mistake).
            if (BugOracle.BlockStateInstrs.Count > 0 && (BugOracle.SendEther || env.Value > 0))
            {
                foreach (int pc in BugOracle.BlockStateInstrs)
                {
                    BugSet.Add((BugClass.BlockstateDependencySFuzz, pc));
                }
            }
        }

        private void CheckMishandledException()
        {
            // Check for unused return value.
            foreach (int pc in BugOracle.UncheckedReturns)
            {
                BugSet.Add((BugClass.MishandledException, pc));
                BugSet.Add((BugClass.MishandledExceptionManticore, pc));
            }
            // Check whether a non top-level exception is silently ignored.
            if (!BugOracle.TopLevelException)
            {
                foreach (int pc in BugOracle.ExceptionReturns)
                {
                    BugSet.Add((BugClass.MishandledExceptionSFuzz, pc));
                    BugSet.Add((BugClass.MishandledExceptionILF, pc));
                }
            }
        }

        // Same logic with the above function, but Mythril checks for ME at different point (STOP/RETURN).
        // Thus, maintain as a separate function.
        private void CheckMishandledExceptionMythril()
        {
            // Check for unused return value.
            foreach (int pc in BugOracle.UncheckedReturns)
            {
                BugSet.Add((BugClass.MishandledExceptionMythril, pc));
            }
        }

        private void CheckReentrancySFuzz(ExecutionEnvironment env)
        {
            // sFuzz checks whether there was a cyclic call and ether transfer.
            // Note that sFuzz also considers env.Value > 0 as ether transfer (this may be a mistake).
            if (BugOracle.CyclicCallPCs.Count > 0 && (BugOracle.SendEther || env.Value > 0))
            {
                foreach (int pc in BugOracle.CyclicCallPCs)
                {
                    BugSet.Add((BugClass.ReentrancySFuzz, pc));
                }
            }
        }

        private void CheckReentrancyILF()
        {
            int lastSend = BugOracle.LastSendPC;
            int lastSStore = BugOracle.LastSStorePC;
            // It's strange to compare the PC (not epoch), but follow the logic of ILF.
            if (lastSend != -1 && lastSStore != -1 && lastSend < lastSStore)
            {
                BugSet.Add((BugClass.ReentrancyILF, lastSStore));
            }
        }

        // Reset states that should not persist between different transactions.
        public void ResetPerTx ()
        {
            BugOracle.ResetPerTx();
            foreach (UInt256 idx in taintStorage.Keys)
            {
                taintStorage[idx].IsSender = false;
                taintStorage[idx].IsBlockStateMythril = false;
            }
        }

        private void LogVisitedEdge (int srcPC, int dstPC)
        {
            int edgeHash = (srcPC << 16) ^ dstPC;
            VisitedEdgeSet.Add(edgeHash);
        }

        private void LogVisitedInstr (int pc)
        {
            VisitedInstrs.Add(pc);
        }

        private void LogException (EvmState currentState, CallResult callResult)
        {
            // Note that 'IsException || ShouldRevert' subsumes the execution of INVALID/REVERT, too.
            bool isError = callResult.IsException || callResult.ShouldRevert;

            // 'IsReturn' indicates the finish of a transaction (not specified to the execution of 'RETURN').
            // Note that we should consider the existence of agent contract when checking the call depth.
            if (currentState.Env.CallDepth == (IsRedirected ? 1 : 0) && callResult.IsReturn && isError)
            {
                BugOracle.TopLevelException = true;
            }
            else if (currentState.Env.CallDepth > (IsRedirected ? 1 : 0) && isError)
            {
                BugOracle.NonTopLevelException = true;
            }
        }

        // can refactor and integrate the other call
        public TransactionSubstate Run(EvmState state, ITxTracer txTracer)
        {
            _txTracer = txTracer;

            IReleaseSpec spec = _specProvider.GetSpec(state.Env.CurrentBlock.Number);
            EvmState currentState = state;
            byte[] previousCallResult = null;
            byte[] previousCallOutput = Bytes.Empty;
            UInt256 previousCallOutputDestination = UInt256.Zero;
            while (true)
            {
                if (!currentState.IsContinuation)
                {
                    _returnDataBuffer = Bytes.Empty;
                }

                try
                {
                    CallResult callResult;
                    if (currentState.IsPrecompile)
                    {
                        if (_txTracer.IsTracingActions)
                        {
                            _txTracer.ReportAction(currentState.GasAvailable, currentState.Env.Value, currentState.From, currentState.To, currentState.Env.InputData, currentState.ExecutionType, true);
                        }

                        callResult = ExecutePrecompile(currentState, spec);

                        LogException(currentState, callResult);

                        if (!callResult.PrecompileSuccess.Value)
                        {
                            if (currentState.IsPrecompile && currentState.IsTopLevel)
                            {
                                Metrics.EvmExceptions++;
                                // TODO: when direct / calls are treated same we should not need such differentiation
                                throw new PrecompileExecutionFailureException();
                            }

                            // TODO: testing it as it seems the way to pass zkSNARKs tests
                            currentState.GasAvailable = 0;
                        }
                    }
                    else
                    {
                        if (_txTracer.IsTracingActions && !currentState.IsContinuation)
                        {
                            _txTracer.ReportAction(currentState.GasAvailable, currentState.Env.Value, currentState.From, currentState.To, currentState.ExecutionType == ExecutionType.Create ? currentState.Env.CodeInfo.MachineCode : currentState.Env.InputData, currentState.ExecutionType);
                            if (_txTracer.IsTracingCode) _txTracer.ReportByteCode(currentState.Env.CodeInfo.MachineCode);
                        }

                        callResult = ExecuteCall(currentState, previousCallResult, previousCallOutput, previousCallOutputDestination, spec);

                        LogException(currentState, callResult);

                        if (!callResult.IsReturn)
                        {
                            _stateStack.Push(currentState);
                            currentState = callResult.StateToExecute;
                            previousCallResult = null; // TODO: testing on ropsten sync, write VirtualMachineTest for this case as it was not covered by Ethereum tests (failing block 9411 on Ropsten https://ropsten.etherscan.io/vmtrace?txhash=0x666194d15c14c54fffafab1a04c08064af165870ef9a87f65711dcce7ed27fe1)
                            _returnDataBuffer = previousCallOutput = Bytes.Empty; // TODO: testing on ropsten sync, write VirtualMachineTest for this case as it was not covered by Ethereum tests
                            continue;
                        }

                        if (callResult.IsException)
                        {
                            if(_txTracer.IsTracingActions) _txTracer.ReportActionError(callResult.ExceptionType);
                            _state.Restore(currentState.StateSnapshot);
                            _storage.Restore(currentState.StorageSnapshot);

                            if (_parityTouchBugAccount != null)
                            {
                                _state.AddToBalance(_parityTouchBugAccount, UInt256.Zero, spec);
                                _parityTouchBugAccount = null;
                            }

                            if (currentState.IsTopLevel)
                            {
                                return new TransactionSubstate("Error");
                            }

                            previousCallResult = StatusCode.FailureBytes;
                            previousCallOutputDestination = UInt256.Zero;
                            _returnDataBuffer = previousCallOutput = Bytes.Empty;

                            currentState.Dispose();
                            currentState = _stateStack.Pop();
                            currentState.IsContinuation = true;
                            continue;
                        }
                    }

                    if (currentState.IsTopLevel)
                    {
                        if (_txTracer.IsTracingActions)
                        {
                            if (callResult.IsException)
                            {
                                _txTracer.ReportActionError(callResult.ExceptionType);
                            }
                            else if (callResult.ShouldRevert)
                            {
                                _txTracer.ReportActionError(EvmExceptionType.Revert);
                            }
                            else
                            {
                                long codeDepositGasCost = CodeDepositHandler.CalculateCost(callResult.Output.Length, spec);
                                if (currentState.ExecutionType == ExecutionType.Create && currentState.GasAvailable < codeDepositGasCost)
                                {
                                    _txTracer.ReportActionError(EvmExceptionType.OutOfGas);
                                }
                                else
                                {
                                    if (currentState.ExecutionType == ExecutionType.Create)
                                    {
                                        _txTracer.ReportActionEnd(currentState.GasAvailable - codeDepositGasCost, currentState.To, callResult.Output);
                                    }
                                    else
                                    {
                                        _txTracer.ReportActionEnd(currentState.GasAvailable, _returnDataBuffer);
                                    }
                                }
                            }
                        }

                        return new TransactionSubstate(callResult.Output, currentState.Refund, currentState.DestroyList, currentState.Logs, callResult.ShouldRevert);
                    }

                    Address callCodeOwner = currentState.Env.ExecutingAccount;
                    EvmState previousState = currentState;
                    currentState = _stateStack.Pop();
                    currentState.IsContinuation = true;
                    currentState.GasAvailable += previousState.GasAvailable;
                    bool previousStateSucceeded = true;

                    if (!callResult.ShouldRevert)
                    {
                        long gasAvailableForCodeDeposit = previousState.GasAvailable; // TODO: refactor, this is to fix 61363 Ropsten
                        if (previousState.ExecutionType == ExecutionType.Create)
                        {
                            previousCallResult = callCodeOwner.Bytes;
                            previousCallOutputDestination = UInt256.Zero;
                            _returnDataBuffer = previousCallOutput = Bytes.Empty;

                            long codeDepositGasCost = CodeDepositHandler.CalculateCost(callResult.Output.Length, spec);
                            if (gasAvailableForCodeDeposit >= codeDepositGasCost)
                            {
                                Keccak codeHash = _state.UpdateCode(callResult.Output);
                                _state.UpdateCodeHash(callCodeOwner, codeHash, spec);
                                currentState.GasAvailable -= codeDepositGasCost;

                                if (_txTracer.IsTracingActions)
                                {
                                    _txTracer.ReportActionEnd(previousState.GasAvailable - codeDepositGasCost, callCodeOwner, callResult.Output);
                                }
                            }
                            else
                            {
                                if (spec.IsEip2Enabled)
                                {
                                    currentState.GasAvailable -= gasAvailableForCodeDeposit;
                                    _state.Restore(previousState.StateSnapshot);
                                    _storage.Restore(previousState.StorageSnapshot);
                                    _state.DeleteAccount(callCodeOwner);
                                    previousCallResult = BytesZero;
                                    previousStateSucceeded = false;

                                    if (_txTracer.IsTracingActions)
                                    {
                                        _txTracer.ReportActionError(EvmExceptionType.OutOfGas);
                                    }
                                }
                            }
                        }
                        else
                        {
                            _returnDataBuffer = callResult.Output;
                            previousCallResult = callResult.PrecompileSuccess.HasValue ? (callResult.PrecompileSuccess.Value ? StatusCode.SuccessBytes : StatusCode.FailureBytes) : StatusCode.SuccessBytes;
                            previousCallOutput = callResult.Output.SliceWithZeroPadding(0, Math.Min(callResult.Output.Length, (int)previousState.OutputLength));
                            previousCallOutputDestination = (ulong)previousState.OutputDestination;
                            if(previousState.IsPrecompile)
                            {
                                // parity induced if else for vmtrace
                                if (_txTracer.IsTracingInstructions)
                                {
                                    _txTracer.ReportMemoryChange((long)previousCallOutputDestination, previousCallOutput);
                                }
                            }

                            if (_txTracer.IsTracingActions)
                            {
                                _txTracer.ReportActionEnd(previousState.GasAvailable, _returnDataBuffer);
                            }
                        }

                        if (previousStateSucceeded)
                        {
                            currentState.Refund += previousState.Refund;

                            foreach (Address address in previousState.DestroyList)
                            {
                                currentState.DestroyList.Add(address);
                            }

                            for (int i = 0; i < previousState.Logs.Count; i++)
                            {
                                LogEntry logEntry = previousState.Logs[i];
                                currentState.Logs.Add(logEntry);
                            }
                        }
                    }
                    else
                    {
                        _state.Restore(previousState.StateSnapshot);
                        _storage.Restore(previousState.StorageSnapshot);
                        _returnDataBuffer = callResult.Output;
                        previousCallResult = StatusCode.FailureBytes;
                        previousCallOutput = callResult.Output.SliceWithZeroPadding(0, Math.Min(callResult.Output.Length, (int)previousState.OutputLength));
                        previousCallOutputDestination = (ulong)previousState.OutputDestination;


                        if (_txTracer.IsTracingActions)
                        {
                            _txTracer.ReportActionError(EvmExceptionType.Revert);
                        }
                    }

                    previousState.Dispose();
                }
                catch (Exception ex) when (ex is EvmException || ex is OverflowException)
                {
                    if (_logger.IsTrace) _logger.Trace($"exception ({ex.GetType().Name}) in {currentState.ExecutionType} at depth {currentState.Env.CallDepth} - restoring snapshot");

                    _state.Restore(currentState.StateSnapshot);
                    _storage.Restore(currentState.StorageSnapshot);

                    if (_parityTouchBugAccount != null)
                    {
                        _state.AddToBalance(_parityTouchBugAccount, UInt256.Zero, spec);
                        _parityTouchBugAccount = null;
                    }

                    if (txTracer.IsTracingInstructions)
                    {
                        txTracer.ReportOperationError((ex as EvmException)?.ExceptionType ?? EvmExceptionType.Other);
                        txTracer.ReportOperationRemainingGas(0);
                    }

                    if (_txTracer.IsTracingActions)
                    {
                        EvmException evmException = ex as EvmException;
                        _txTracer.ReportActionError(evmException?.ExceptionType ?? EvmExceptionType.Other);
                    }

                    if (currentState.IsTopLevel)
                    {
                        return new TransactionSubstate("Error");
                    }

                    previousCallResult = StatusCode.FailureBytes;
                    previousCallOutputDestination = UInt256.Zero;
                    _returnDataBuffer = previousCallOutput = Bytes.Empty;

                    currentState.Dispose();
                    currentState = _stateStack.Pop();
                    currentState.IsContinuation = true;
                }
            }
        }

        public CodeInfo GetCachedCodeInfo(Address codeSource)
        {
            Keccak codeHash = _state.GetCodeHash(codeSource);
            CodeInfo cachedCodeInfo = _codeCache.Get(codeHash);
            if (cachedCodeInfo == null)
            {
                byte[] code = _state.GetCode(codeHash);
                if (code == null)
                {
                    throw new NullReferenceException($"Code {codeHash} missing in the state for address {codeSource}");
                }

                cachedCodeInfo = new CodeInfo(code);
                _codeCache.Set(codeHash, cachedCodeInfo);
            }

            return cachedCodeInfo;
        }

        public void DisableSimdInstructions()
        {
            _simdOperationsEnabled = false;
        }

        private void InitializePrecompiledContracts()
        {
            _precompiles = new Dictionary<Address, IPrecompiledContract>
            {
                [EcRecoverPrecompiledContract.Instance.Address] = EcRecoverPrecompiledContract.Instance,
                [Sha256PrecompiledContract.Instance.Address] = Sha256PrecompiledContract.Instance,
                [Ripemd160PrecompiledContract.Instance.Address] = Ripemd160PrecompiledContract.Instance,
                [IdentityPrecompiledContract.Instance.Address] = IdentityPrecompiledContract.Instance,
                [Bn128AddPrecompiledContract.Instance.Address] = Bn128AddPrecompiledContract.Instance,
                [Bn128MulPrecompiledContract.Instance.Address] = Bn128MulPrecompiledContract.Instance,
                [Bn128PairingPrecompiledContract.Instance.Address] = Bn128PairingPrecompiledContract.Instance,
                [ModExpPrecompiledContract.Instance.Address] = ModExpPrecompiledContract.Instance,
                [Blake2BPrecompiledContract.Instance.Address] = Blake2BPrecompiledContract.Instance,
            };
        }

        private bool UpdateGas(long gasCost, ref long gasAvailable)
        {
            if (gasAvailable < gasCost)
            {
                Metrics.EvmExceptions++;
                return false;
            }

            gasAvailable -= gasCost;
            return true;
        }

        private void RefundGas(long refund, ref long gasAvailable)
        {
            gasAvailable += refund;
        }

        private CallResult ExecutePrecompile(EvmState state, IReleaseSpec spec)
        {
            byte[] callData = state.Env.InputData;
            UInt256 transferValue = state.Env.TransferValue;
            long gasAvailable = state.GasAvailable;

            IPrecompiledContract precompile = _precompiles[state.Env.CodeInfo.PrecompileAddress];
            long baseGasCost = precompile.BaseGasCost(spec);
            long dataGasCost = precompile.DataGasCost(callData, spec);

            bool wasCreated = false;
            if (!_state.AccountExists(state.Env.ExecutingAccount))
            {
                wasCreated = true;
                _state.CreateAccount(state.Env.ExecutingAccount, transferValue);
            }
            else
            {
                _state.AddToBalance(state.Env.ExecutingAccount, transferValue, spec);
            }

            if (gasAvailable < dataGasCost + baseGasCost)
            {
                // https://github.com/ethereum/EIPs/blob/master/EIPS/eip-161.md
                // An additional issue was found in Parity,
                // where the Parity client incorrectly failed
                // to revert empty account deletions in a more limited set of contexts
                // involving out-of-gas calls to precompiled contracts;
                // the new Geth behavior matches Parity’s,
                // and empty accounts will cease to be a source of concern in general
                // in about one week once the state clearing process finishes.

                if (!wasCreated && transferValue.IsZero && spec.IsEip158Enabled)
                {
                    _parityTouchBugAccount = state.Env.ExecutingAccount;
                }

                Metrics.EvmExceptions++;
                throw new OutOfGasException();
            }

            //if(!UpdateGas(dataGasCost, ref gasAvailable)) return CallResult.Exception;
            if (!UpdateGas(baseGasCost, ref gasAvailable))
            {
                throw new OutOfGasException();
            }

            if (!UpdateGas(dataGasCost, ref gasAvailable))
            {
                throw new OutOfGasException();
            }

            state.GasAvailable = gasAvailable;

            try
            {
                (byte[] output, bool success) = precompile.Run(callData);
                CallResult callResult = new CallResult(output, success);
                return callResult;
            }
            catch (Exception)
            {
                CallResult callResult = new CallResult(new byte[0], false);
                return callResult;
            }
        }

        private CallResult ExecuteCall(EvmState evmState, byte[] previousCallResult, byte[] previousCallOutput, in UInt256 previousCallOutputDestination, IReleaseSpec spec)
        {
            bool isTrace = _logger.IsTrace;
            bool traceOpcodes = _txTracer.IsTracingInstructions;
            ExecutionEnvironment env = evmState.Env;
            if (!evmState.IsContinuation)
            {
                if (!_state.AccountExists(env.ExecutingAccount))
                {
                    _state.CreateAccount(env.ExecutingAccount, env.TransferValue);
                }
                else
                {
                    _state.AddToBalance(env.ExecutingAccount, env.TransferValue, spec);
                }

                if (evmState.ExecutionType == ExecutionType.Create && spec.IsEip158Enabled)
                {
                    _state.IncrementNonce(env.ExecutingAccount);
                }
            }

            if (evmState.Env.CodeInfo.MachineCode == null || evmState.Env.CodeInfo.MachineCode.Length == 0)
            {
                return CallResult.Empty;
            }

            evmState.InitStacks();
            Span<byte> bytesOnStack = evmState.BytesOnStack.AsSpan();
            int stackHead = evmState.StackHead;
            long gasAvailable = evmState.GasAvailable;
            int programCounter = evmState.ProgramCounter;
            Span<byte> code = env.CodeInfo.MachineCode.AsSpan();

            bool isTestingTarget = IsDeployingTarget || IsTargetContract(env.ExecutingAccount);
            Stack<TaintInfo> taintStack = new Stack<TaintInfo>(evmState.TaintStack);
            Dictionary<UInt256, TaintInfo> taintMemory = new Dictionary <UInt256, TaintInfo> (evmState.TaintMemory);

            int CountFollowingIsZero(Span<byte> code, int pc)
            {
                int count = 0;
                if ((Instruction) code[pc] == Instruction.ISZERO)
                {
                    count += 1;
                    if (code.Length > pc + 1 && (Instruction) code[pc + 1] == Instruction.ISZERO)
                    {
                        count += 1;
                        if (code.Length > pc + 2 && (Instruction) code[pc + 2] == Instruction.ISZERO)
                        {
                            count += 1;
                        }
                    }
                }
                return count;
            }

            void UpdateCurrentState()
            {
                evmState.ProgramCounter = programCounter;
                evmState.GasAvailable = gasAvailable;
                evmState.StackHead = stackHead;
                evmState.TaintStack = new Stack<TaintInfo>(taintStack);
                evmState.TaintMemory = new Dictionary<UInt256, TaintInfo>(taintMemory);
            }

            void StartInstructionTrace(Instruction instruction, Span<byte> stack)
            {
                if (!traceOpcodes)
                {
                    return;
                }

                _txTracer.StartOperation(env.CallDepth + 1, gasAvailable, instruction, programCounter);
                if (_txTracer.IsTracingMemory) { _txTracer.SetOperationMemory(evmState.Memory.GetTrace()); }
                if (_txTracer.IsTracingStack) { _txTracer.SetOperationStack(GetStackTrace(stack)); }
            }

            void EndInstructionTrace()
            {
                if (traceOpcodes)
                {
                    if (_txTracer.IsTracingMemory)
                    {
                        _txTracer.SetOperationMemorySize(evmState.Memory.Size);
                    }

                    _txTracer.ReportOperationRemainingGas(gasAvailable);
                }
            }

            void EndInstructionTraceError(EvmExceptionType evmExceptionType)
            {
                if (traceOpcodes)
                {
                    _txTracer.ReportOperationError(evmExceptionType);
                    _txTracer.ReportOperationRemainingGas(gasAvailable);
                }
            }

            void PushBytes(Span<byte> value, Span<byte> stack)
            {
                if (_txTracer.IsTracingInstructions) _txTracer.ReportStackPush(value);

                if (value.Length != 32)
                {
                    stack.Slice(stackHead * 32, 32 - value.Length).Clear();
                }

                value.CopyTo(stack.Slice(stackHead * 32 + (32 - value.Length), value.Length));
                stackHead++;
                if (stackHead >= MaxStackSize)
                {
                    Metrics.EvmExceptions++;
                    throw new EvmStackOverflowException();
                }
            }

            void PushLeftPaddedBytes(Span<byte> value, int paddingLength, Span<byte> stack)
            {
                if (_txTracer.IsTracingInstructions) _txTracer.ReportStackPush(value);

                if (value.Length != 32)
                {
                    stack.Slice(stackHead * 32, 32).Clear();
                }

                value.CopyTo(stack.Slice(stackHead * 32 + 32 - paddingLength, value.Length));
                stackHead++;
                if (stackHead >= MaxStackSize)
                {
                    Metrics.EvmExceptions++;
                    throw new EvmStackOverflowException();
                }
            }

            void PushByte(byte value, Span<byte> stack)
            {
                if (_txTracer.IsTracingInstructions) _txTracer.ReportStackPush(new byte[] {value});

                stack.Slice(stackHead * 32, 32).Clear();
                stack[stackHead * 32 + 31] = value;
                stackHead++;

                if (stackHead >= MaxStackSize)
                {
                    Metrics.EvmExceptions++;
                    throw new EvmStackOverflowException();
                }
            }

            void PushOne(Span<byte> stack)
            {
                if (_txTracer.IsTracingInstructions) _txTracer.ReportStackPush(new byte[] {1});

                stack.Slice(stackHead * 32, 32).Clear();
                stack[stackHead * 32 + 31] = 1;
                stackHead++;
                if (stackHead >= MaxStackSize)
                {
                    Metrics.EvmExceptions++;
                    throw new EvmStackOverflowException();
                }
            }

            void PushZero(Span<byte> stack)
            {
                if (_txTracer.IsTracingInstructions) _txTracer.ReportStackPush(new byte[] {0});

                stack.Slice(stackHead * 32, 32).Clear();
                stackHead++;
                if (stackHead >= MaxStackSize)
                {
                    Metrics.EvmExceptions++;
                    throw new EvmStackOverflowException();
                }
            }

            void PushUInt256(ref UInt256 value, Span<byte> stack)
            {
                Span<byte> target = stack.Slice(stackHead * 32, 32);
                value.ToBigEndian(target);

                if (_txTracer.IsTracingInstructions) _txTracer.ReportStackPush(target);

                stackHead++;
                if (stackHead >= MaxStackSize)
                {
                    Metrics.EvmExceptions++;
                    throw new EvmStackOverflowException();
                }
            }

            void PushUInt(ref BigInteger value, Span<byte> stack)
            {
                Span<byte> target = stack.Slice(stackHead * 32, 32);
                int bytesToWrite = value.GetByteCount(true);
                if (bytesToWrite != 32)
                {
                    target.Clear();
                    target = target.Slice(32 - bytesToWrite, bytesToWrite);
                }

                value.TryWriteBytes(target, out int bytesWritten, true, true);

                if (_txTracer.IsTracingInstructions) _txTracer.ReportStackPush(target);

                stackHead++;
                if (stackHead >= MaxStackSize)
                {
                    Metrics.EvmExceptions++;
                    throw new EvmStackOverflowException();
                }
            }

            void PushSignedInt(ref BigInteger value, Span<byte> stack)
            {
                Span<byte> target = stack.Slice(stackHead * 32, 32);
                int bytesToWrite = value.GetByteCount(false);
                bool treatAsUnsigned = bytesToWrite == 33;
                if (treatAsUnsigned)
                {
                    bytesToWrite = 32;
                }

                if (bytesToWrite != 32)
                {
                    if (value.Sign >= 0)
                    {
                        target.Clear();
                    }
                    else
                    {
                        target.Fill(0xff);
                    }

                    target = target.Slice(32 - bytesToWrite, bytesToWrite);
                }

                value.TryWriteBytes(target, out int bytesWritten, treatAsUnsigned, true);

                if (_txTracer.IsTracingInstructions) _txTracer.ReportStackPush(target);

                stackHead++;
                if (stackHead >= MaxStackSize)
                {
                    Metrics.EvmExceptions++;
                    throw new EvmStackOverflowException();
                }
            }

            void PopLimbo()
            {
                if (stackHead == 0)
                {
                    Metrics.EvmExceptions++;
                    throw new EvmStackUnderflowException();
                }

                stackHead--;
            }

            void Dup(int depth, Span<byte> stack)
            {
                if (stackHead < depth)
                {
                    Metrics.EvmExceptions++;
                    throw new EvmStackUnderflowException();
                }

                stack.Slice((stackHead - depth) * 32, 32).CopyTo(stack.Slice(stackHead * 32, 32));
                if (_txTracer.IsTracingInstructions)
                {
                    for (int i = depth; i >= 0; i--)
                    {
                        _txTracer.ReportStackPush(stack.Slice(stackHead * 32 - i * 32, 32));
                    }
                }

                stackHead++;
                if (stackHead >= MaxStackSize)
                {
                    Metrics.EvmExceptions++;
                    throw new EvmStackOverflowException();
                }
            }

            Span<byte> wordBuffer = stackalloc byte[32];
            void Swap(int depth, Span<byte> stack, Span<byte> buffer)
            {
                if (stackHead < depth)
                {
                    Metrics.EvmExceptions++;
                    throw new EvmStackUnderflowException();
                }

                Span<byte> bottomSpan = stack.Slice((stackHead - depth) * 32, 32);
                Span<byte> topSpan = stack.Slice((stackHead - 1) * 32, 32);

                bottomSpan.CopyTo(buffer);
                topSpan.CopyTo(bottomSpan);
                buffer.CopyTo(topSpan);

                if (_txTracer.IsTracingInstructions)
                {
                    for (int i = depth; i > 0; i--)
                    {
                        _txTracer.ReportStackPush(stack.Slice(stackHead * 32 - i * 32, 32));
                    }
                }
            }

            // ReSharper disable once ImplicitlyCapturedClosure
            Span<byte> PopBytes(Span<byte> stack)
            {
                if (stackHead == 0)
                {
                    Metrics.EvmExceptions++;
                    throw new EvmStackUnderflowException();
                }

                stackHead--;

                return stack.Slice(stackHead * 32, 32);
            }

            byte PopByte(Span<byte> stack)
            {
                if (stackHead == 0)
                {
                    Metrics.EvmExceptions++;
                    throw new EvmStackUnderflowException();
                }

                stackHead--;

                return stack[stackHead * 32 + 31];
            }

            List<string> GetStackTrace(Span<byte> stack)
            {
                List<string> stackTrace = new List<string>();
                for (int i = 0; i < stackHead; i++)
                {
                    Span<byte> stackItem = stack.Slice(i * 32, 32);
                    stackTrace.Add(stackItem.ToArray().ToHexString());
                }

                return stackTrace;
            }

            void PopUInt256(out UInt256 result, Span<byte> stack)
            {
                UInt256.CreateFromBigEndian(out result, PopBytes(stack));
            }

            void PopUInt(out BigInteger result, Span<byte> stack)
            {
                result = PopBytes(stack).ToUnsignedBigInteger();
            }

            void PopInt(out BigInteger result, Span<byte> stack)
            {
                result = PopBytes(stack).ToSignedBigInteger(32);
            }

            Address PopAddress(Span<byte> stack)
            {
                if (stackHead == 0)
                {
                    Metrics.EvmExceptions++;
                    throw new EvmStackUnderflowException();
                }

                stackHead--;

                return new Address(stack.Slice(stackHead * 32 + 12, 20).ToArray());
            }

            void UpdateMemoryCost(ref UInt256 position, in UInt256 length)
            {
                long memoryCost = evmState.Memory.CalculateMemoryCost(ref position, length);
                if (memoryCost != 0L)
                {
                    if (!UpdateGas(memoryCost, ref gasAvailable))
                    {
                        Metrics.EvmExceptions++;
                        EndInstructionTraceError(OutOfGasErrorText);
                        throw new OutOfGasException();
                    }
                }
            }

            void BinOpTaintStack()
            {
                TaintInfo newTaint = new TaintInfo(taintStack.Pop());
                newTaint.Join(taintStack.Pop());
                taintStack.Push(newTaint);
            }

            // Addmod, submod, mulmod, etc.
            void TernOpTaintStack()
            {
                TaintInfo newTaint = new TaintInfo(taintStack.Pop());
                newTaint.Join(taintStack.Pop());
                newTaint.Join(taintStack.Pop());
                taintStack.Push(newTaint);
            }

            // IsZero.
            void UnaryCmpOpTaintStack()
            {
                // We will preserve taint propagation for NEG/NOT operations, too.
                TaintInfo newTaint = new TaintInfo(taintStack.Pop());
                taintStack.Push(newTaint);
            }

            // LT, GT, EQ, etc.
            void BinCmpOpTaintStack()
            {
                // We will preserve taint propagation for compare operations, too.
                TaintInfo newTaint = new TaintInfo(taintStack.Pop());
                newTaint.Join(taintStack.Pop());
                taintStack.Push(newTaint);
            }

            void CheckStackConsistency(string spot)
            {
                if (stackHead != taintStack.Count)
                {
                  Console.WriteLine("Inconsistent stack @ 0x" + (programCounter - 1).ToString("X"));
                  Console.WriteLine(spot + ": " + stackHead.ToString() + " vs. " + taintStack.Count.ToString());
                }
            }

            void PushNonTainted()
            {
                taintStack.Push(TaintInfo.Bot());
            }

            void PushOriginTainted()
            {
                taintStack.Push(TaintInfo.Origin());
            }

            void PushSenderTainted()
            {
                taintStack.Push(TaintInfo.Sender());
            }

            void PushReturnTainted(int pc)
            {
                taintStack.Push(TaintInfo.Return(pc));
            }

            void PushBlockTainted(Instruction ins, bool isOldBlock = false)
            {
                taintStack.Push(TaintInfo.BlockState(ins, isOldBlock));
            }

            if (previousCallResult != null)
            {
                if(isTestingTarget)
                {
                    BugOracle.UncheckedReturns.Add(programCounter - 1);
                    if (BugOracle.NonTopLevelException)
                    {
                        BugOracle.ExceptionReturns.Add(programCounter - 1);
                        BugOracle.NonTopLevelException = false;
                    }
                }
                PushBytes(previousCallResult, bytesOnStack);
                PushReturnTainted(programCounter - 1);
                CheckStackConsistency("ExecuteCall() entry");
                if(_txTracer.IsTracingInstructions) _txTracer.ReportOperationRemainingGas(evmState.GasAvailable);
            }

            if (previousCallOutput.Length > 0)
            {
                UInt256 localPreviousDest = previousCallOutputDestination;
                UpdateMemoryCost(ref localPreviousDest, (ulong)previousCallOutput.Length);
                evmState.Memory.Save(ref localPreviousDest, previousCallOutput);
//                if(_txTracer.IsTracingInstructions) _txTracer.ReportMemoryChange((long)localPreviousDest, previousCallOutput);
            }

            while (programCounter < code.Length)
            {
                if (isTestingTarget)
                {
                    LogVisitedInstr(programCounter);
                }

                Instruction instruction = (Instruction)code[(int)programCounter];
                if (traceOpcodes)
                {
                    StartInstructionTrace(instruction, bytesOnStack);
                }

                programCounter++;
                switch (instruction)
                {
                    case Instruction.STOP:
                    {
                        if (isTestingTarget)
                        {
                            CheckMishandledExceptionMythril();
                        }
                        UpdateCurrentState();
                        EndInstructionTrace();
                        return CallResult.Empty;
                    }
                    case Instruction.ADD:
                    {
                        if (!UpdateGas(GasCostOf.VeryLow, ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        // TODO: can calculate in place...
                        PopUInt256(out UInt256 b, bytesOnStack);
                        PopUInt256(out UInt256 a, bytesOnStack);
                        UInt256.Add(out UInt256 c, ref a, ref b, false);
                        PushUInt256(ref c, bytesOnStack);

                        TaintInfo newTaint = new TaintInfo(taintStack.Pop());
                        newTaint.Join(taintStack.Pop());
                        BigInteger test = BigInteger.Add(a, b);
                        bool overflowed = (c != test);
                        if (overflowed)
                        {
                            newTaint.OvfSrcs.Add(programCounter - 1);
                            if (isTestingTarget)
                            {
                                BugSet.Add((BugClass.IntegerBugSFuzz, programCounter - 1));
                            }
                        }
                        taintStack.Push(newTaint);
                        CheckStackConsistency("ADD");

                        break;
                    }
                    case Instruction.MUL:
                    {
                        if (!UpdateGas(GasCostOf.Low, ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        PopUInt(out BigInteger a, bytesOnStack);
                        PopUInt(out BigInteger b, bytesOnStack);
                        BigInteger res = BigInteger.Remainder(a * b, P256Int);
                        PushUInt(ref res, bytesOnStack);

                        TaintInfo newTaint = new TaintInfo(taintStack.Pop());
                        newTaint.Join(taintStack.Pop());
                        BigInteger test = BigInteger.Multiply(a, b);
                        bool overflowed = (res != test);
                        if (overflowed)
                        {
                            newTaint.OvfSrcs.Add(programCounter - 1);
                        }
                        taintStack.Push(newTaint);
                        CheckStackConsistency("MUL");

                        break;
                    }
                    case Instruction.SUB:
                    {
                        if (!UpdateGas(GasCostOf.VeryLow, ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        // TODO: can calculate in place...
                        PopUInt256(out UInt256 a, bytesOnStack);
                        PopUInt256(out UInt256 b, bytesOnStack);
                        UInt256 result = a - b;

                        PushUInt256(ref result, bytesOnStack);

                        TaintInfo newTaint = new TaintInfo(taintStack.Pop());
                        newTaint.Join(taintStack.Pop());
                        bool overflowed = a < b;
                        if (overflowed)
                        {
                            newTaint.OvfSrcs.Add(programCounter - 1);
                            if (isTestingTarget)
                            {
                                BugSet.Add((BugClass.IntegerBugSFuzz, programCounter - 1));
                            }
                        }
                        taintStack.Push(newTaint);
                        CheckStackConsistency("SUB");

                        break;
                    }
                    case Instruction.DIV:
                    {
                        if (!UpdateGas(GasCostOf.Low, ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        // TODO: can calculate in place...
                        PopUInt(out BigInteger a, bytesOnStack);
                        PopUInt(out BigInteger b, bytesOnStack);
                        if (b.IsZero)
                        {
                            PushZero(bytesOnStack);
                        }
                        else
                        {
                            BigInteger res = BigInteger.Divide(a, b);
                            PushUInt(ref res, bytesOnStack);
                        }

                        // Slightly over-taint when b is 0.
                        BinOpTaintStack();
                        CheckStackConsistency("DIV");

                        break;
                    }
                    case Instruction.SDIV:
                    {
                        if (!UpdateGas(GasCostOf.Low, ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        PopInt(out BigInteger a, bytesOnStack);
                        PopInt(out BigInteger b, bytesOnStack);
                        if (b.IsZero)
                        {
                            PushZero(bytesOnStack);
                        }
                        else if (b == BigInteger.MinusOne && a == P255Int)
                        {
                            BigInteger res = P255;
                            PushUInt(ref res, bytesOnStack);
                        }
                        else
                        {
                            BigInteger res = BigInteger.Divide(a, b);
                            PushSignedInt(ref res, bytesOnStack);
                        }

                        // Slightly over-taint when b is 0.
                        BinOpTaintStack();
                        CheckStackConsistency("SDIV");

                        break;
                    }
                    case Instruction.MOD:
                    {
                        if (!UpdateGas(GasCostOf.Low, ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        PopUInt(out BigInteger a, bytesOnStack);
                        PopUInt(out BigInteger b, bytesOnStack);
                        BigInteger res = b.IsZero ? BigInteger.Zero : BigInteger.Remainder(a, b);
                        PushUInt(ref res, bytesOnStack);

                        // Slightly over-taint when b is 0.
                        BinOpTaintStack();
                        CheckStackConsistency("MOD");

                        break;
                    }
                    case Instruction.SMOD:
                    {
                        if (!UpdateGas(GasCostOf.Low, ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        PopInt(out BigInteger a, bytesOnStack);
                        PopInt(out BigInteger b, bytesOnStack);
                        if (b.IsZero)
                        {
                            PushZero(bytesOnStack);
                        }
                        else
                        {
                            BigInteger res = a.Sign * BigInteger.Remainder(a.Abs(), b.Abs());
                            PushSignedInt(ref res, bytesOnStack);
                        }

                        // Slightly over-taint when b is 0.
                        BinOpTaintStack();
                        CheckStackConsistency("SMOD");

                        break;
                    }
                    case Instruction.ADDMOD:
                    {
                        if (!UpdateGas(GasCostOf.Mid, ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        PopUInt(out BigInteger a, bytesOnStack);
                        PopUInt(out BigInteger b, bytesOnStack);
                        PopUInt(out BigInteger mod, bytesOnStack);

                        if (mod.IsZero)
                        {
                            PushZero(bytesOnStack);
                        }
                        else
                        {
                            BigInteger res = BigInteger.Remainder(a + b, mod);
                            PushUInt(ref res, bytesOnStack);
                        }

                        // Slightly over-taint when mod is 0.
                        TernOpTaintStack();
                        CheckStackConsistency("ADDMOD");

                        break;
                    }
                    case Instruction.MULMOD:
                    {
                        if (!UpdateGas(GasCostOf.Mid, ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        PopUInt(out BigInteger a, bytesOnStack);
                        PopUInt(out BigInteger b, bytesOnStack);
                        PopUInt(out BigInteger mod, bytesOnStack);

                        if (mod.IsZero)
                        {
                            PushZero(bytesOnStack);
                        }
                        else
                        {
                            BigInteger res = BigInteger.Remainder(a * b, mod);
                            PushUInt(ref res, bytesOnStack);
                        }

                        // Slightly over-taint when mod is 0.
                        TernOpTaintStack();
                        CheckStackConsistency("MULMOD");

                        break;
                    }
                    case Instruction.EXP:
                    {
                        if (!UpdateGas(GasCostOf.Exp, ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        Metrics.ModExpOpcode++;

                        PopUInt(out BigInteger baseInt, bytesOnStack);
                        Span<byte> exp = PopBytes(bytesOnStack);

                        int leadingZeros = exp.LeadingZerosCount();
                        if (leadingZeros != 32)
                        {
                            int expSize = 32 - leadingZeros;
                            if (!UpdateGas((spec.IsEip160Enabled ? GasCostOf.ExpByteEip160 : GasCostOf.ExpByte) * expSize, ref gasAvailable))
                            {
                                EndInstructionTraceError(OutOfGasErrorText);
                                return CallResult.OutOfGasException;
                            }
                        }
                        else
                        {
                            PushOne(bytesOnStack);

                            // Slightly over-taint when exp is 0.
                            BinOpTaintStack();
                            CheckStackConsistency("EXP");

                            break;
                        }

                        if (baseInt.IsZero)
                        {
                            PushZero(bytesOnStack);
                        }
                        else if (baseInt.IsOne)
                        {
                            PushOne(bytesOnStack);
                        }
                        else
                        {
                            BigInteger res = BigInteger.ModPow(baseInt, exp.ToUnsignedBigInteger(), P256Int);
                            PushUInt(ref res, bytesOnStack);
                        }

                        // Slightly over-taint when base is 0/1.
                        BinOpTaintStack();
                        CheckStackConsistency("EXP");

                        break;
                    }
                    case Instruction.SIGNEXTEND:
                    {
                        if (!UpdateGas(GasCostOf.Low, ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        PopUInt(out BigInteger a, bytesOnStack);
                        if (a >= BigInt32)
                        {
                            break;
                        }

                        int position = 31 - (int)a;

                        Span<byte> b = PopBytes(bytesOnStack);
                        sbyte sign = (sbyte)b[position];

                        if (sign >= 0)
                        {
                            BytesZero32.AsSpan(0, position).CopyTo(b.Slice(0, position));
                        }
                        else
                        {
                            BytesMax32.AsSpan(0, position).CopyTo(b.Slice(0, position));
                        }

                        PushBytes(b, bytesOnStack);

                        BinOpTaintStack();
                        CheckStackConsistency("SIGNEXTEND");

                        break;
                    }
                    case Instruction.LT:
                    {
                        if (!UpdateGas(GasCostOf.VeryLow, ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        PopUInt(out BigInteger a, bytesOnStack);
                        PopUInt(out BigInteger b, bytesOnStack);

                        int followingIsZeros = CountFollowingIsZero(code, programCounter);
                        if (followingIsZeros == 0 || followingIsZeros == 2)
                        {
                            CmpList.Add((programCounter - 1, "<u", a, b));
                        }
                        else // One or three negations.
                        {
                            CmpList.Add((programCounter - 1, ">=u", a, b));
                        }

                        if (a < b)
                        {
                            PushOne(bytesOnStack);
                        }
                        else
                        {
                            PushZero(bytesOnStack);
                        }

                        BinCmpOpTaintStack();
                        CheckStackConsistency("LT");

                        break;
                    }
                    case Instruction.GT:
                    {
                        if (!UpdateGas(GasCostOf.VeryLow, ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        PopUInt(out BigInteger a, bytesOnStack);
                        PopUInt(out BigInteger b, bytesOnStack);

                        int followingIsZeros = CountFollowingIsZero(code, programCounter);
                        if (followingIsZeros == 0 || followingIsZeros == 2)
                        {
                            CmpList.Add((programCounter - 1, ">u", a, b));
                        }
                        else // One or three negations.
                        {
                            CmpList.Add((programCounter - 1, "<=u", a, b));
                        }

                        if (a > b)
                        {
                            PushOne(bytesOnStack);
                        }
                        else
                        {
                            PushZero(bytesOnStack);
                        }

                        BinCmpOpTaintStack();
                        CheckStackConsistency("GT");

                        break;
                    }
                    case Instruction.SLT:
                    {
                        if (!UpdateGas(GasCostOf.VeryLow, ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        PopInt(out BigInteger a, bytesOnStack);
                        PopInt(out BigInteger b, bytesOnStack);

                        int followingIsZeros = CountFollowingIsZero(code, programCounter);
                        if (followingIsZeros == 0 || followingIsZeros == 2)
                        {
                            CmpList.Add((programCounter - 1, "<s", a, b));
                        }
                        else // One or three negations.
                        {
                            CmpList.Add((programCounter - 1, ">=s", a, b));
                        }

                        if (BigInteger.Compare(a, b) < 0)
                        {
                            PushOne(bytesOnStack);
                        }
                        else
                        {
                            PushZero(bytesOnStack);
                        }

                        BinCmpOpTaintStack();
                        CheckStackConsistency("SLT");

                        break;
                    }
                    case Instruction.SGT:
                    {
                        if (!UpdateGas(GasCostOf.VeryLow, ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        PopInt(out BigInteger a, bytesOnStack);
                        PopInt(out BigInteger b, bytesOnStack);

                        int followingIsZeros = CountFollowingIsZero(code, programCounter);
                        if (followingIsZeros == 0 || followingIsZeros == 2)
                        {
                            CmpList.Add((programCounter - 1, ">s", a, b));
                        }
                        else // One or three negations.
                        {
                            CmpList.Add((programCounter - 1, "<=s", a, b));
                        }

                        if (BigInteger.Compare(a, b) > 0)
                        {
                            PushOne(bytesOnStack);
                        }
                        else
                        {
                            PushZero(bytesOnStack);
                        }

                        BinCmpOpTaintStack();
                        CheckStackConsistency("SGT");

                        break;
                    }
                    case Instruction.EQ:
                    {
                        if (!UpdateGas(GasCostOf.VeryLow, ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        Span<byte> a = PopBytes(bytesOnStack);
                        Span<byte> b = PopBytes(bytesOnStack);

                        BigInteger ba = a.ToUnsignedBigInteger ();
                        BigInteger bb = b.ToUnsignedBigInteger ();

                        int followingIsZeros = CountFollowingIsZero(code, programCounter);
                        if (followingIsZeros == 0 || followingIsZeros == 2)
                        {
                            CmpList.Add((programCounter - 1, "==", ba, bb));
                        }
                        else // One or three negations.
                        {
                            CmpList.Add((programCounter - 1, "!=", ba, bb));
                        }

                        if (a.SequenceEqual(b))
                        {
                            PushOne(bytesOnStack);
                        }
                        else
                        {
                            PushZero(bytesOnStack);
                        }

                        BinCmpOpTaintStack();
                        CheckStackConsistency("EQ");

                        break;
                    }
                    case Instruction.ISZERO:
                    {
                        if (!UpdateGas(GasCostOf.VeryLow, ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        Span<byte> a = PopBytes(bytesOnStack);
                        if (a.SequenceEqual(BytesZero32))
                        {
                            PushOne(bytesOnStack);
                        }
                        else
                        {
                            PushZero(bytesOnStack);
                        }

                        UnaryCmpOpTaintStack();
                        CheckStackConsistency("ISZERO");

                        break;
                    }
                    case Instruction.AND:
                    {
                        if (!UpdateGas(GasCostOf.VeryLow, ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        Span<byte> a = PopBytes(bytesOnStack);
                        Span<byte> b = PopBytes(bytesOnStack);

                        if (_simdOperationsEnabled)
                        {
                            Vector<byte> aVec = new Vector<byte>(a);
                            Vector<byte> bVec = new Vector<byte>(b);

                            Vector.BitwiseAnd(aVec, bVec).CopyTo(wordBuffer);
                        }
                        else
                        {
                            for (int i = 0; i < 32; i++)
                            {
                                wordBuffer[i] = (byte)(a[i] & b[i]);
                            }
                        }

                        PushBytes(wordBuffer, bytesOnStack);

                        BinOpTaintStack();
                        CheckStackConsistency("AND");

                        break;
                    }
                    case Instruction.OR:
                    {
                        if (!UpdateGas(GasCostOf.VeryLow, ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        Span<byte> a = PopBytes(bytesOnStack);
                        Span<byte> b = PopBytes(bytesOnStack);

                        if (_simdOperationsEnabled)
                        {
                            Vector<byte> aVec = new Vector<byte>(a);
                            Vector<byte> bVec = new Vector<byte>(b);

                            Vector.BitwiseOr(aVec, bVec).CopyTo(wordBuffer);
                        }
                        else
                        {
                            for (int i = 0; i < 32; i++)
                            {
                                wordBuffer[i] = (byte)(a[i] | b[i]);
                            }
                        }

                        PushBytes(wordBuffer, bytesOnStack);

                        BinOpTaintStack();
                        CheckStackConsistency("OR");

                        break;
                    }
                    case Instruction.XOR:
                    {
                        if (!UpdateGas(GasCostOf.VeryLow, ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        Span<byte> a = PopBytes(bytesOnStack);
                        Span<byte> b = PopBytes(bytesOnStack);

                        if (_simdOperationsEnabled)
                        {
                            Vector<byte> aVec = new Vector<byte>(a);
                            Vector<byte> bVec = new Vector<byte>(b);

                            Vector.Xor(aVec, bVec).CopyTo(wordBuffer);
                        }
                        else
                        {
                            for (int i = 0; i < 32; i++)
                            {
                                wordBuffer[i] = (byte)(a[i] ^ b[i]);
                            }
                        }

                        PushBytes(wordBuffer, bytesOnStack);

                        BinOpTaintStack();
                        CheckStackConsistency("XOR");

                        break;
                    }
                    case Instruction.NOT:
                    {
                        if (!UpdateGas(GasCostOf.VeryLow, ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        Span<byte> a = PopBytes(bytesOnStack);

                        if (_simdOperationsEnabled)
                        {
                            Vector<byte> aVec = new Vector<byte>(a);
                            Vector<byte> negVec = Vector.Xor(aVec, new Vector<byte>(BytesMax32));

                            negVec.CopyTo(wordBuffer);
                        }
                        else
                        {
                            for (int i = 0; i < 32; ++i)
                            {
                                wordBuffer[i] = (byte)~a[i];
                            }
                        }

                        PushBytes(wordBuffer, bytesOnStack);

                        // Taint stack remains the same.
                        CheckStackConsistency("NOT");

                        break;
                    }
                    case Instruction.BYTE:
                    {
                        if (!UpdateGas(GasCostOf.VeryLow, ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        PopUInt(out BigInteger position, bytesOnStack);
                        Span<byte> bytes = PopBytes(bytesOnStack);

                        if (position >= BigInt32)
                        {
                            PushZero(bytesOnStack);
                            break;
                        }

                        int adjustedPosition = bytes.Length - 32 + (int)position;
                        if (adjustedPosition < 0)
                        {
                            PushZero(bytesOnStack);
                        }
                        else
                        {
                            PushByte(bytes[adjustedPosition], bytesOnStack);
                        }

                        // Slightly over-taint when position is invalid.
                        BinOpTaintStack();
                        CheckStackConsistency("BYTE");

                        break;
                    }
                    case Instruction.SHA3:
                    {
                        PopUInt256(out UInt256 memSrc, bytesOnStack);
                        PopUInt256(out UInt256 memLength, bytesOnStack);

                        taintStack.Pop();
                        taintStack.Pop();

                        if (!UpdateGas(GasCostOf.Sha3 + GasCostOf.Sha3Word * EvmPooledMemory.Div32Ceiling(memLength),
                            ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        UpdateMemoryCost(ref memSrc, memLength);

                        Span<byte> memData = evmState.Memory.LoadSpan(ref memSrc, memLength);
                        PushBytes(ValueKeccak.Compute(memData).BytesAsSpan, bytesOnStack);

                        TaintInfo newTaint = TaintInfo.Bot();
                        for (UInt256 i = 0; i < memLength; i++)
                        {
                            if (taintMemory.ContainsKey(memSrc + i))
                            {
                                newTaint.JoinDependency(taintMemory[memSrc + i]);
                            }
                        }
                        taintStack.Push(newTaint);
                        CheckStackConsistency("SHA3");

                        break;
                    }
                    case Instruction.ADDRESS:
                    {
                        if (!UpdateGas(GasCostOf.Base, ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        PushBytes(env.ExecutingAccount.Bytes, bytesOnStack);

                        PushNonTainted();
                        CheckStackConsistency("ADDRESS");

                        break;
                    }
                    case Instruction.BALANCE:
                    {
                        var gasCost = spec.IsEip1884Enabled
                            ? GasCostOf.BalanceEip1884
                            : spec.IsEip150Enabled
                                ? GasCostOf.BalanceEip150
                                : GasCostOf.Balance;

                        if (!UpdateGas(gasCost, ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        Address address = PopAddress(bytesOnStack);
                        UInt256 balance = _state.GetBalance(address);
                        PushUInt256(ref balance, bytesOnStack);

                        taintStack.Pop();
                        PushNonTainted();
                        CheckStackConsistency("BALANCE");

                        break;
                    }
                    case Instruction.CALLER:
                    {
                        if (!UpdateGas(GasCostOf.Base, ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        PushBytes(env.Sender.Bytes, bytesOnStack);

                        PushSenderTainted();
                        CheckStackConsistency("CALLER");

                        break;
                    }
                    case Instruction.CALLVALUE:
                    {
                        if (!UpdateGas(GasCostOf.Base, ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        UInt256 callValue = env.Value;
                        PushUInt256(ref callValue, bytesOnStack);

                        PushNonTainted();
                        CheckStackConsistency("CALLVALUE");

                        break;
                    }
                    case Instruction.ORIGIN:
                    {
                        if (!UpdateGas(GasCostOf.Base, ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        if (isTestingTarget)
                        {
                            BugSet.Add((BugClass.BlockstateDependencyManticore, programCounter - 1));
                        }

                        PushBytes(env.Originator.Bytes, bytesOnStack);

                        PushOriginTainted();
                        CheckStackConsistency("ORIGIN");

                        break;
                    }
                    case Instruction.CALLDATALOAD:
                    {
                        if (!UpdateGas(GasCostOf.VeryLow, ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        PopUInt(out BigInteger src, bytesOnStack);
                        PushBytes(env.InputData.SliceWithZeroPadding(src, 32), bytesOnStack);

                        taintStack.Pop();
                        PushNonTainted();
                        CheckStackConsistency("CALLDATALOAD");

                        break;
                    }
                    case Instruction.CALLDATASIZE:
                    {
                        if (!UpdateGas(GasCostOf.Base, ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        BigInteger callDataSize = env.InputData.Length;
                        PushUInt(ref callDataSize, bytesOnStack);

                        PushNonTainted();
                        CheckStackConsistency("CALLDATASIZE");

                        break;
                    }
                    case Instruction.CALLDATACOPY:
                    {
                        PopUInt256(out UInt256 dest, bytesOnStack);
                        PopUInt256(out UInt256 src, bytesOnStack);
                        PopUInt256(out UInt256 length, bytesOnStack);

                        taintStack.Pop();
                        taintStack.Pop();
                        taintStack.Pop();
                        CheckStackConsistency("CALLDATACOPY");

                        if (!UpdateGas(GasCostOf.VeryLow + GasCostOf.Memory * EvmPooledMemory.Div32Ceiling(length),
                            ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        UpdateMemoryCost(ref dest, length);

                        byte[] callDataSlice = env.InputData.SliceWithZeroPadding(src, (int)length);
                        evmState.Memory.Save(ref dest, callDataSlice);
                        if(_txTracer.IsTracingInstructions) _txTracer.ReportMemoryChange((long)dest, callDataSlice);
                        break;
                    }
                    case Instruction.CODESIZE:
                    {
                        if (!UpdateGas(GasCostOf.Base, ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        BigInteger codeLength = code.Length;
                        PushUInt(ref codeLength, bytesOnStack);

                        PushNonTainted();
                        CheckStackConsistency("CODESIZE");

                        break;
                    }
                    case Instruction.CODECOPY:
                    {
                        PopUInt256(out UInt256 dest, bytesOnStack);
                        PopUInt256(out UInt256 src, bytesOnStack);
                        PopUInt256(out UInt256 length, bytesOnStack);

                        taintStack.Pop();
                        taintStack.Pop();
                        taintStack.Pop();
                        CheckStackConsistency("CODECOPY");

                        if (!UpdateGas(GasCostOf.VeryLow + GasCostOf.Memory * EvmPooledMemory.Div32Ceiling(length), ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        UpdateMemoryCost(ref dest, length);
                        Span<byte> codeSlice = code.SliceWithZeroPadding(src, (int)length);
                        evmState.Memory.Save(ref dest, codeSlice);
                        if(_txTracer.IsTracingInstructions) _txTracer.ReportMemoryChange((long)dest, codeSlice);
                        break;
                    }
                    case Instruction.GASPRICE:
                    {
                        if (!UpdateGas(GasCostOf.Base, ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        if (isTestingTarget)
                        {
                            BugSet.Add((BugClass.BlockstateDependencyManticore, programCounter - 1));
                        }

                        UInt256 gasPrice = env.GasPrice;
                        PushUInt256(ref gasPrice, bytesOnStack);

                        PushNonTainted();
                        CheckStackConsistency("GASPRICE");

                        break;
                    }
                    case Instruction.EXTCODESIZE:
                    {
                        if (!UpdateGas(spec.IsEip150Enabled ? GasCostOf.ExtCodeSizeEip150 : GasCostOf.ExtCodeSize, ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        Address address = PopAddress(bytesOnStack);
                        byte[] accountCode = GetCachedCodeInfo(address)?.MachineCode;
                        BigInteger codeSize = accountCode?.Length ?? BigInteger.Zero;
                        PushUInt(ref codeSize, bytesOnStack);

                        taintStack.Pop();
                        PushNonTainted();
                        CheckStackConsistency("EXTCODESIZE");

                        break;
                    }
                    case Instruction.EXTCODECOPY:
                    {
                        Address address = PopAddress(bytesOnStack);
                        PopUInt256(out UInt256 dest, bytesOnStack);
                        PopUInt256(out UInt256 src, bytesOnStack);
                        PopUInt256(out UInt256 length, bytesOnStack);

                        taintStack.Pop();
                        taintStack.Pop();
                        taintStack.Pop();
                        CheckStackConsistency("EXTCODECOPY");

                        if (!UpdateGas((spec.IsEip150Enabled ? GasCostOf.ExtCodeEip150 : GasCostOf.ExtCode) + GasCostOf.Memory * EvmPooledMemory.Div32Ceiling(length),
                            ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        UpdateMemoryCost(ref dest, length);
                        byte[] externalCode = GetCachedCodeInfo(address)?.MachineCode;
                        byte[] callDataSlice = externalCode.SliceWithZeroPadding(src, (int)length);
                        evmState.Memory.Save(ref dest, callDataSlice);
                        if(_txTracer.IsTracingInstructions) _txTracer.ReportMemoryChange((long)dest, callDataSlice);
                        break;
                    }
                    case Instruction.RETURNDATASIZE:
                    {
                        if (!spec.IsEip211Enabled)
                        {
                            Metrics.EvmExceptions++;
                            EndInstructionTraceError(BadInstructionErrorText);
                            return CallResult.InvalidInstructionException;
                        }

                        if (!UpdateGas(GasCostOf.Base, ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        BigInteger res = _returnDataBuffer.Length;
                        PushUInt(ref res, bytesOnStack);

                        PushNonTainted();
                        CheckStackConsistency("RETURNDATASIZE");

                        break;
                    }
                    case Instruction.RETURNDATACOPY:
                    {
                        if (!spec.IsEip211Enabled)
                        {
                            Metrics.EvmExceptions++;
                            EndInstructionTraceError(BadInstructionErrorText);
                            return CallResult.InvalidInstructionException;
                        }

                        PopUInt256(out UInt256 dest, bytesOnStack);
                        PopUInt256(out UInt256 src, bytesOnStack);
                        PopUInt256(out UInt256 length, bytesOnStack);

                        taintStack.Pop();
                        taintStack.Pop();
                        taintStack.Pop();
                        CheckStackConsistency("RETURNDATACOPY");

                        if (!UpdateGas(GasCostOf.VeryLow + GasCostOf.Memory * EvmPooledMemory.Div32Ceiling(length), ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        UpdateMemoryCost(ref dest, length);

                        if (UInt256.AddWouldOverflow(ref length, ref src) || length + src > _returnDataBuffer.Length)
                        {
                            Metrics.EvmExceptions++;
                            return CallResult.AccessViolationException;
                        }

                        byte[] returnDataSlice = _returnDataBuffer.SliceWithZeroPadding(src, (int)length);
                        evmState.Memory.Save(ref dest, returnDataSlice);
                        if(_txTracer.IsTracingInstructions) _txTracer.ReportMemoryChange((long)dest, returnDataSlice);
                        break;
                    }
                    case Instruction.BLOCKHASH:
                    {
                        Metrics.BlockhashOpcode++;

                        if (!UpdateGas(GasCostOf.BlockHash, ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        if (isTestingTarget)
                        {
                            BugSet.Add((BugClass.BlockstateDependencyManticore, programCounter - 1));
                        }

                        PopUInt256(out UInt256 a, bytesOnStack);
                        long number = a > long.MaxValue ? long.MaxValue : (long)a;
                        PushBytes(_blockhashProvider.GetBlockhash(env.CurrentBlock, number)?.Bytes ?? BytesZero32, bytesOnStack);

                        taintStack.Pop();
                        PushBlockTainted(instruction, number < env.CurrentBlock.Number);
                        CheckStackConsistency("BLOCKHASH");

                        break;
                    }
                    case Instruction.COINBASE:
                    {
                        if (!UpdateGas(GasCostOf.Base, ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        if (isTestingTarget)
                        {
                            BugSet.Add((BugClass.BlockstateDependencyManticore, programCounter - 1));
                        }

                        PushBytes(env.CurrentBlock.GasBeneficiary.Bytes, bytesOnStack);

                        PushBlockTainted(instruction);
                        CheckStackConsistency("COINBASE");

                        break;
                    }
                    case Instruction.DIFFICULTY:
                    {
                        if (!UpdateGas(GasCostOf.Base, ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        if (isTestingTarget)
                        {
                            BugSet.Add((BugClass.BlockstateDependencyManticore, programCounter - 1));
                        }

                        UInt256 diff = env.CurrentBlock.Difficulty;
                        PushUInt256(ref diff, bytesOnStack);

                        PushBlockTainted(instruction);
                        CheckStackConsistency("DIFFICULTY");

                        break;
                    }
                    case Instruction.TIMESTAMP:
                    {
                        if (!UpdateGas(GasCostOf.Base, ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        if (isTestingTarget)
                        {
                            BugOracle.BlockStateInstrs.Add(programCounter - 1);
                            BugSet.Add((BugClass.BlockstateDependencyManticore, programCounter - 1));
                        }

                        UInt256 timestamp = env.CurrentBlock.Timestamp;
                        PushUInt256(ref timestamp, bytesOnStack);

                        PushBlockTainted(instruction);
                        CheckStackConsistency("TIMESTAMP");

                        break;
                    }
                    case Instruction.NUMBER:
                    {
                        if (!UpdateGas(GasCostOf.Base, ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        if (isTestingTarget)
                        {
                            BugOracle.BlockStateInstrs.Add(programCounter - 1);
                            BugSet.Add((BugClass.BlockstateDependencyManticore, programCounter - 1));
                        }

                        UInt256 blockNumber = (UInt256)env.CurrentBlock.Number;
                        PushUInt256(ref blockNumber, bytesOnStack);

                        PushBlockTainted(instruction);
                        CheckStackConsistency("NUMBER");

                        break;
                    }
                    case Instruction.GASLIMIT:
                    {
                        if (!UpdateGas(GasCostOf.Base, ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        if (isTestingTarget)
                        {
                            BugSet.Add((BugClass.BlockstateDependencyManticore, programCounter - 1));
                        }

                        UInt256 gasLimit = (UInt256)env.CurrentBlock.GasLimit;
                        PushUInt256(ref gasLimit, bytesOnStack);
                        break;
                    }
                    case Instruction.CHAINID:
                    {
                        if (!spec.IsEip1344Enabled)
                        {
                            Metrics.EvmExceptions++;
                            EndInstructionTraceError(BadInstructionErrorText);
                            return CallResult.InvalidInstructionException;
                        }

                        if (!UpdateGas(GasCostOf.Base, ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        PushBytes(_chainId, bytesOnStack);

                        PushNonTainted();
                        CheckStackConsistency("CHAINID");

                        break;
                    }
                    case Instruction.SELFBALANCE:
                    {
                        if (!spec.IsEip1884Enabled)
                        {
                            Metrics.EvmExceptions++;
                            EndInstructionTraceError(BadInstructionErrorText);
                            return CallResult.InvalidInstructionException;
                        }

                        if (!UpdateGas(GasCostOf.SelfBalance, ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        UInt256 balance = _state.GetBalance(env.ExecutingAccount);
                        PushUInt256(ref balance, bytesOnStack);

                        PushNonTainted();
                        CheckStackConsistency("SELFBALANCE");

                        break;
                    }
                    case Instruction.POP:
                    {
                        if (!UpdateGas(GasCostOf.Base, ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        PopLimbo();

                        taintStack.Pop();
                        CheckStackConsistency("POP");

                        break;
                    }
                    case Instruction.MLOAD:
                    {
                        if (!UpdateGas(GasCostOf.VeryLow, ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        PopUInt256(out UInt256 memPosition, bytesOnStack);
                        UpdateMemoryCost(ref memPosition, 32);
                        Span<byte> memData = evmState.Memory.LoadSpan(ref memPosition);
                        if(_txTracer.IsTracingInstructions) _txTracer.ReportMemoryChange((long)memPosition, memData);

                        PushBytes(memData, bytesOnStack);

                        // Propagate the taintness from memory to stack.
                        TaintInfo idxTaint = new TaintInfo(taintStack.Pop());
                        TaintInfo valTaint;
                        if (taintMemory.ContainsKey(memPosition))
                        {
                            valTaint = new TaintInfo(taintMemory[memPosition]);
                        }
                        else
                        {
                            valTaint = TaintInfo.Bot();
                        }
                        // Consider index-based indirect flow for block state taintness.
                        if (idxTaint.IsBlockState)
                        {
                            valTaint.IsBlockState = true;
                        }
                        taintStack.Push(valTaint);
                        CheckStackConsistency("MLOAD");

                        break;
                    }
                    case Instruction.MSTORE:
                    {
                        if (!UpdateGas(GasCostOf.VeryLow, ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        PopUInt256(out UInt256 memPosition, bytesOnStack);
                        Span<byte> data = PopBytes(bytesOnStack);
                        UpdateMemoryCost(ref memPosition, 32);
                        evmState.Memory.SaveWord(ref memPosition, data);
                        if(_txTracer.IsTracingInstructions) _txTracer.ReportMemoryChange((long)memPosition, data.PadLeft(32));

                        // Propagate the taintness from stack to memory
                        taintStack.Pop();
                        TaintInfo valTaint = taintStack.Pop();
                        for (UInt256 i = 0; i < 32; i++)
                        {
                            taintMemory[memPosition + i] = new TaintInfo(valTaint);
                        }
                        CheckStackConsistency("MSTORE");

                        break;
                    }
                    case Instruction.MSTORE8:
                    {
                        if (!UpdateGas(GasCostOf.VeryLow, ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        PopUInt256(out UInt256 memPosition, bytesOnStack);
                        byte data = PopByte(bytesOnStack);
                        UpdateMemoryCost(ref memPosition, UInt256.One);
                        evmState.Memory.SaveByte(ref memPosition, data);
                        if(_txTracer.IsTracingInstructions) _txTracer.ReportMemoryChange((long)memPosition, new [] {data});

                        // Propagate the taintness from stack to memory.
                        taintStack.Pop();
                        TaintInfo valTaint = taintStack.Pop();
                        taintMemory[memPosition] = new TaintInfo(valTaint);
                        CheckStackConsistency("MSTORE8");

                        break;
                    }
                    case Instruction.SLOAD:
                    {
                        Metrics.SloadOpcode++;
                        var gasCost = spec.IsEip1884Enabled
                            ? GasCostOf.SLoadEip1884
                            : spec.IsEip150Enabled
                                ? GasCostOf.SLoadEip150
                                : GasCostOf.SLoad;

                        if (!UpdateGas(gasCost, ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        PopUInt256(out UInt256 storageIndex, bytesOnStack);
                        byte[] value = _storage.Get(new StorageAddress(env.ExecutingAccount, storageIndex));
                        PushBytes(value, bytesOnStack);

                        // Propagate taintness from storage to stack.
                        TaintInfo idxTaint = new TaintInfo(taintStack.Pop());
                        TaintInfo valTaint;
                        if (taintStorage.ContainsKey(storageIndex))
                        {
                            valTaint = new TaintInfo(taintStorage[storageIndex]);
                        }
                        else
                        {
                            valTaint = TaintInfo.Bot();
                        }
                        // Consider index-based indirect flow for block state taintness.
                        if (idxTaint.IsBlockState)
                        {
                            valTaint.IsBlockState = true;
                        }
                        valTaint.VarSrcs.Clear();
                        valTaint.VarSrcs.Add(storageIndex);
                        taintStack.Push(valTaint);
                        CheckStackConsistency("SLOAD");

                        if (isTestingTarget && TraceDU && !IsDeployingTarget && DefPCMap.ContainsKey(storageIndex))
                        {
                            // Update def-use chain set.
                            DefUseChainSet.Add((DefPCMap[storageIndex], programCounter - 1, storageIndex));
                        }

                        break;
                    }
                    case Instruction.SSTORE:
                    {
                        Metrics.SstoreOpcode++;

                        if (evmState.IsStatic)
                        {
                            Metrics.EvmExceptions++;
                            return CallResult.StaticCallViolationException;
                        }

                        bool useNetMetering = spec.IsEip1283Enabled | spec.IsEip2200Enabled;
                        // fail fast before the first storage read if gas is not enough even for reset
                        if (!useNetMetering && !UpdateGas(GasCostOf.SReset, ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        if (spec.IsEip2200Enabled && gasAvailable <= GasCostOf.CallStipend)
                        {
                            Metrics.EvmExceptions++;
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        PopUInt256(out UInt256 storageIndex, bytesOnStack);
                        byte[] newValue = PopBytes(bytesOnStack).WithoutLeadingZeros().ToArray();
                        bool newIsZero = newValue.IsZero();

                        StorageAddress storageAddress = new StorageAddress(env.ExecutingAccount, storageIndex);
                        byte[] currentValue = _storage.Get(storageAddress);
                        bool currentIsZero = currentValue.IsZero();

                        bool newSameAsCurrent = (newIsZero && currentIsZero) || Bytes.AreEqual(currentValue, newValue);

                        if (!useNetMetering) // note that for this case we already deducted 5000
                        {
                            if (newIsZero)
                            {
                                if (!newSameAsCurrent)
                                {
                                    evmState.Refund += RefundOf.SClear;
                                    if(_txTracer.IsTracingInstructions) _txTracer.ReportRefund(RefundOf.SClear);
                                }
                            }
                            else if (currentIsZero)
                            {
                                if (!UpdateGas(GasCostOf.SSet - GasCostOf.SReset, ref gasAvailable))
                                {
                                    EndInstructionTraceError(OutOfGasErrorText);
                                    return CallResult.OutOfGasException;
                                }
                            }
                        }
                        else // net metered
                        {
                            if (newSameAsCurrent)
                            {
                                long netMeteredStoreCost = spec.IsEip2200Enabled ? GasCostOf.SStoreNetMeteredEip2200 : GasCostOf.SStoreNetMeteredEip1283;
                                if(!UpdateGas(netMeteredStoreCost, ref gasAvailable))
                                {
                                    EndInstructionTraceError(OutOfGasErrorText);
                                    return CallResult.OutOfGasException;
                                }
                            }
                            else // eip1283enabled, C != N
                            {
                                byte[] originalValue = _storage.GetOriginal(storageAddress);
                                bool originalIsZero = originalValue.IsZero();

                                bool currentSameAsOriginal = Bytes.AreEqual(originalValue, currentValue);
                                if (currentSameAsOriginal)
                                {
                                    if (currentIsZero)
                                    {
                                        if (!UpdateGas(GasCostOf.SSet, ref gasAvailable))
                                        {
                                            EndInstructionTraceError(OutOfGasErrorText);
                                            return CallResult.OutOfGasException;
                                        }
                                    }
                                    else // eip1283enabled, current == original != new, !currentIsZero
                                    {
                                        if (!UpdateGas(GasCostOf.SReset, ref gasAvailable))
                                        {
                                            EndInstructionTraceError(OutOfGasErrorText);
                                            return CallResult.OutOfGasException;
                                        }

                                        if (newIsZero)
                                        {
                                            evmState.Refund += RefundOf.SClear;
                                            if(_txTracer.IsTracingInstructions) _txTracer.ReportRefund(RefundOf.SClear);
                                        }
                                    }
                                }
                                else // net metered, new != current != original
                                {
                                    long netMeteredStoreCost = spec.IsEip2200Enabled ? GasCostOf.SStoreNetMeteredEip2200 : GasCostOf.SStoreNetMeteredEip1283;
                                    if (!UpdateGas(netMeteredStoreCost, ref gasAvailable))
                                    {
                                        EndInstructionTraceError(OutOfGasErrorText);
                                        return CallResult.OutOfGasException;
                                    }

                                    if (!originalIsZero) // net metered, new != current != original != 0
                                    {
                                        if (currentIsZero)
                                        {
                                            evmState.Refund -= RefundOf.SClear;
                                            if(_txTracer.IsTracingInstructions) _txTracer.ReportRefund(-RefundOf.SClear);
                                        }

                                        if (newIsZero)
                                        {
                                            evmState.Refund += RefundOf.SClear;
                                            if(_txTracer.IsTracingInstructions) _txTracer.ReportRefund(RefundOf.SClear);
                                        }
                                    }

                                    bool newSameAsOriginal = Bytes.AreEqual(originalValue, newValue);
                                    if(newSameAsOriginal)
                                    {
                                        long refundFromReversal;
                                        if (originalIsZero)
                                        {
                                            refundFromReversal = spec.IsEip2200Enabled ? RefundOf.SSetReversedEip2200 : RefundOf.SSetReversedEip1283;
                                        }
                                        else
                                        {
                                            refundFromReversal = spec.IsEip2200Enabled ? RefundOf.SClearReversedEip2200 : RefundOf.SClearReversedEip1283;
                                        }

                                        evmState.Refund += refundFromReversal;
                                        if(_txTracer.IsTracingInstructions) _txTracer.ReportRefund(refundFromReversal);
                                    }
                                }
                            }
                        }

                        if (!newSameAsCurrent)
                        {
                            byte[] valueToStore = newIsZero ? BytesZero : newValue;
                            _storage.Set(storageAddress, valueToStore);
                        }

                        // Propagate the taintness from stack to storage.
                        taintStack.Pop();
                        TaintInfo valTaint = new TaintInfo(taintStack.Pop());
                        if (BugOracle.FlowAffectedByBlockState)
                        {
                            // Note that ILF/Mythril don't propagate indirect taint flows.
                            valTaint.IsBlockState = true;
                        }
                        HashSet<int> ovfPCs = new HashSet<int>(valTaint.OvfSrcs); // Caution: should copy, not assign.
                        // Now reset the overflow sources, since we are already raising an alarm here.
                        valTaint.OvfSrcs.Clear();
                        taintStorage[storageIndex] = valTaint;

                        CheckStackConsistency("SSTORE");

                        if (isTestingTarget)
                        {
                            // Smartian, Mythril, and Manticore all report IB alarms if an overflowed value is stored into the storage.
                            foreach (int pc in ovfPCs)
                            {
                                BugSet.Add((BugClass.IntegerBug, pc));
                                BugSet.Add((BugClass.IntegerBugMythril, pc));
                                BugSet.Add((BugClass.IntegerBugManticore, pc));
                            }

                            // Check if we are updating a variable that had affected a cyclic call.
                            if (BugOracle.CheckAffectOnCyclicCall(storageIndex))
                            {
                                BugSet.Add((BugClass.Reentrancy, programCounter - 1));
                            }

                            // ILF records the PC of (the latest) SSTORE and compares PCs later.
                            BugOracle.LastSStorePC = programCounter - 1;

                            // Manticore checks whether an SSTORE instruction comes after an external call.
                            if (BugOracle.HadExternCall)
                            {
                                BugSet.Add((BugClass.ReentrancyManticore, programCounter - 1));
                            }

                            BigInteger a = storageIndex;
                            BigInteger b = 0xdeadcafe; // Arbitrary magic value.
                            CmpList.Add((programCounter - 1, "==", a, b));
                            if (a == b)
                            {
                                BugSet.Add((BugClass.ArbitraryWrite, programCounter - 1));
                            }
                        }

                        if (isTestingTarget && TraceDU && !IsDeployingTarget) {
                            DefPCMap[storageIndex] = programCounter - 1;
                        }

                        if (_txTracer.IsTracingInstructions)
                        {
                            byte[] valueToStore = newIsZero ? BytesZero : newValue;
                            Span<byte> span = new byte[32]; // do not stackalloc here
                            storageAddress.Index.ToBigEndian(span);
                            _txTracer.ReportStorageChange(span, valueToStore);
                        }

                        if (_txTracer.IsTracingOpLevelStorage)
                        {
                            _txTracer.SetOperationStorage(storageAddress.Address, storageIndex, newValue, currentValue);
                        }

                        break;
                    }
                    case Instruction.JUMP:
                    {
                        if (!UpdateGas(GasCostOf.Mid, ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        PopUInt256(out UInt256 jumpDest, bytesOnStack);

                        BigInteger a = jumpDest;
                        BigInteger b = 0xdead; // Arbitrary magic value that is small enough.
                        CmpList.Add((programCounter - 1, "==", a, b));
                        if (a == b)
                        {
                            BugSet.Add((BugClass.ControlHijack, programCounter - 1));
                        }

                        if (jumpDest > int.MaxValue)
                        {
                            Metrics.EvmExceptions++;
                            EndInstructionTraceError(EvmExceptionType.InvalidJumpDestination);
                            // https://github.com/NethermindEth/nethermind/issues/140
                            throw new InvalidJumpDestinationException();
//                            return CallResult.InvalidJumpDestination;
                        }

                        int jumpDestInt = (int)jumpDest;
                        if (!env.CodeInfo.ValidateJump(jumpDestInt))
                        {
                            // https://github.com/NethermindEth/nethermind/issues/140
                            EndInstructionTraceError(EvmExceptionType.InvalidJumpDestination);
                            throw new InvalidJumpDestinationException();
//                            return CallResult.InvalidJumpDestination;
                        }

                        taintStack.Pop();
                        CheckStackConsistency("JUMP");

                        if (isTestingTarget)
                        {
                            LogVisitedEdge(programCounter - 1, jumpDestInt);
                        }

                        programCounter = jumpDestInt;
                        break;
                    }
                    case Instruction.JUMPI:
                    {
                        if (!UpdateGas(GasCostOf.High, ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        PopUInt256(out UInt256 jumpDest, bytesOnStack);
                        Span<byte> condition = PopBytes(bytesOnStack);

                        taintStack.Pop();
                        TaintInfo condTaint = taintStack.Pop();
                        CheckStackConsistency("JUMPI");

                        if (isTestingTarget)
                        {
                            foreach (int pc in condTaint.OvfSrcs)
                            {
                                BugSet.Add((BugClass.IntegerBugMythril, pc));
                            }
                            BugOracle.VarsUsedForCond.UnionWith(condTaint.VarSrcs);
                            BugOracle.UncheckedReturns.ExceptWith(condTaint.ReturnSrcs);
                            if (condTaint.IsBlockState)
                            {
                                BugOracle.FlowAffectedByBlockState = true;
                            }
                            if (condTaint.IsBlockStateILF)
                            {
                                BugOracle.FlowAffectedByBlockStateILF = true;
                            }
                            if (condTaint.IsBlockStateMythril)
                            {
                                BugSet.Add((BugClass.BlockstateDependencyMythril, programCounter - 1));
                            }
                            if (condTaint.IsOrigin && !condTaint.IsSender) // Filter out checks like "msg.sender == tx.origin".
                            {
                                BugSet.Add((BugClass.TransactionOriginUse, programCounter - 1));
                            }
                        }

                        if (!condition.SequenceEqual(BytesZero32))
                        {
                            if (jumpDest > int.MaxValue)
                            {
                                Metrics.EvmExceptions++;
                                EndInstructionTraceError(EvmExceptionType.InvalidJumpDestination);
                                // https://github.com/NethermindEth/nethermind/issues/140
                                throw new InvalidJumpDestinationException();
//                                return CallResult.InvalidJumpDestination; // TODO: add a test, validating inside the condition was not covered by existing tests and fails on 0xf435a354924097686ea88dab3aac1dd464e6a3b387c77aeee94145b0fa5a63d2 mainnet
                            }

                            int jumpDestInt = (int)jumpDest;

                            if (!env.CodeInfo.ValidateJump(jumpDestInt))
                            {
                                EndInstructionTraceError(EvmExceptionType.InvalidJumpDestination);
                                // https://github.com/NethermindEth/nethermind/issues/140
                                throw new InvalidJumpDestinationException();
//                                return CallResult.InvalidJumpDestination; // TODO: add a test, validating inside the condition was not covered by existing tests and fails on 61363 Ropsten
                            }

                            if (isTestingTarget)
                            {
                                LogVisitedEdge(programCounter - 1, jumpDestInt);
                            }

                            programCounter = jumpDestInt;
                        }
                        else // Jump not taken.
                        {
                            if (isTestingTarget)
                            {
                                LogVisitedEdge(programCounter - 1, programCounter);
                            }
                        }

                        break;
                    }
                    case Instruction.PC:
                    {
                        if (!UpdateGas(GasCostOf.Base, ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        UInt256 pc = (UInt256)(programCounter - 1);
                        PushUInt256(ref pc, bytesOnStack);

                        PushNonTainted();
                        CheckStackConsistency("PC");

                        break;
                    }
                    case Instruction.MSIZE:
                    {
                        if (!UpdateGas(GasCostOf.Base, ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        UInt256 size = evmState.Memory.Size;
                        PushUInt256(ref size, bytesOnStack);

                        PushNonTainted();
                        CheckStackConsistency("MSIZE");

                        break;
                    }
                    case Instruction.GAS:
                    {
                        if (!UpdateGas(GasCostOf.Base, ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        UInt256 gas = (UInt256)gasAvailable;
                        PushUInt256(ref gas, bytesOnStack);

                        PushNonTainted();
                        CheckStackConsistency("GAS");

                        break;
                    }
                    case Instruction.JUMPDEST:
                    {
                        if (!UpdateGas(GasCostOf.JumpDest, ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        break;
                    }
                    case Instruction.PUSH1:
                    {
                        if (!UpdateGas(GasCostOf.VeryLow, ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        int programCounterInt = (int)programCounter;
                        if (programCounterInt >= code.Length)
                        {
                            PushZero(bytesOnStack);
                        }
                        else
                        {
                            PushByte(code[programCounterInt], bytesOnStack);
                        }

                        PushNonTainted();
                        CheckStackConsistency("PUSH1");

                        programCounter++;
                        break;
                    }
                    case Instruction.PUSH2:
                    case Instruction.PUSH3:
                    case Instruction.PUSH4:
                    case Instruction.PUSH5:
                    case Instruction.PUSH6:
                    case Instruction.PUSH7:
                    case Instruction.PUSH8:
                    case Instruction.PUSH9:
                    case Instruction.PUSH10:
                    case Instruction.PUSH11:
                    case Instruction.PUSH12:
                    case Instruction.PUSH13:
                    case Instruction.PUSH14:
                    case Instruction.PUSH15:
                    case Instruction.PUSH16:
                    case Instruction.PUSH17:
                    case Instruction.PUSH18:
                    case Instruction.PUSH19:
                    case Instruction.PUSH20:
                    case Instruction.PUSH21:
                    case Instruction.PUSH22:
                    case Instruction.PUSH23:
                    case Instruction.PUSH24:
                    case Instruction.PUSH25:
                    case Instruction.PUSH26:
                    case Instruction.PUSH27:
                    case Instruction.PUSH28:
                    case Instruction.PUSH29:
                    case Instruction.PUSH30:
                    case Instruction.PUSH31:
                    case Instruction.PUSH32:
                    {
                        if (!UpdateGas(GasCostOf.VeryLow, ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        int length = instruction - Instruction.PUSH1 + 1;
                        int programCounterInt = programCounter;
                        int usedFromCode = Math.Min(code.Length - programCounterInt, length);

                        PushLeftPaddedBytes(code.Slice(programCounterInt, usedFromCode), length, bytesOnStack);

                        PushNonTainted();
                        CheckStackConsistency("PUSH*");

                        programCounter += length;
                        break;
                    }
                    case Instruction.DUP1:
                    case Instruction.DUP2:
                    case Instruction.DUP3:
                    case Instruction.DUP4:
                    case Instruction.DUP5:
                    case Instruction.DUP6:
                    case Instruction.DUP7:
                    case Instruction.DUP8:
                    case Instruction.DUP9:
                    case Instruction.DUP10:
                    case Instruction.DUP11:
                    case Instruction.DUP12:
                    case Instruction.DUP13:
                    case Instruction.DUP14:
                    case Instruction.DUP15:
                    case Instruction.DUP16:
                    {
                        if (!UpdateGas(GasCostOf.VeryLow, ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        Dup(instruction - Instruction.DUP1 + 1, bytesOnStack);

                        TaintInfo [] taintArray = taintStack.ToArray();
                        taintStack.Push(taintArray[instruction - Instruction.DUP1]);
                        CheckStackConsistency("DUP*");

                        break;
                    }
                    case Instruction.SWAP1:
                    case Instruction.SWAP2:
                    case Instruction.SWAP3:
                    case Instruction.SWAP4:
                    case Instruction.SWAP5:
                    case Instruction.SWAP6:
                    case Instruction.SWAP7:
                    case Instruction.SWAP8:
                    case Instruction.SWAP9:
                    case Instruction.SWAP10:
                    case Instruction.SWAP11:
                    case Instruction.SWAP12:
                    case Instruction.SWAP13:
                    case Instruction.SWAP14:
                    case Instruction.SWAP15:
                    case Instruction.SWAP16:
                    {
                        if (!UpdateGas(GasCostOf.VeryLow, ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        Swap(instruction - Instruction.SWAP1 + 2, bytesOnStack, wordBuffer);

                        TaintInfo [] arr = taintStack.ToArray();
                        TaintInfo tmp = arr[0];
                        arr[0] = arr[instruction - Instruction.SWAP1 + 1];
                        arr[instruction - Instruction.SWAP1 + 1] = tmp;
                        Array.Reverse(arr);
                        taintStack = new Stack<TaintInfo>(arr);
                        CheckStackConsistency("SWAP*");

                        break;
                    }
                    case Instruction.LOG0:
                    case Instruction.LOG1:
                    case Instruction.LOG2:
                    case Instruction.LOG3:
                    case Instruction.LOG4:
                    {
                        if (evmState.IsStatic)
                        {
                            Metrics.EvmExceptions++;
                            return CallResult.StaticCallViolationException;
                        }

                        PopUInt256(out UInt256 memoryPos, bytesOnStack);
                        PopUInt256(out UInt256 length, bytesOnStack);

                        taintStack.Pop();
                        taintStack.Pop();
                        CheckStackConsistency("LOG* (1)");

                        long topicsCount = instruction - Instruction.LOG0;
                        UpdateMemoryCost(ref memoryPos, length);
                        if (!UpdateGas(
                            GasCostOf.Log + topicsCount * GasCostOf.LogTopic +
                            (long)length * GasCostOf.LogData, ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        byte[] data = evmState.Memory.Load(ref memoryPos, length);
                        Keccak[] topics = new Keccak[topicsCount];
                        for (int i = 0; i < topicsCount; i++)
                        {
                            topics[i] = new Keccak(PopBytes(bytesOnStack).ToArray());
                            taintStack.Pop();
                        }

                        LogEntry logEntry = new LogEntry(
                            env.ExecutingAccount,
                            data,
                            topics);
                        evmState.Logs.Add(logEntry);

                        CheckStackConsistency("LOG* (2)");

                        break;
                    }
                    case Instruction.CREATE:
                    case Instruction.CREATE2:
                    {
                        if(!spec.IsEip1014Enabled && instruction == Instruction.CREATE2)
                        {
                            EndInstructionTraceError(BadInstructionErrorText);
                            return CallResult.InvalidInstructionException;
                        }

                        if (evmState.IsStatic)
                        {
                            Metrics.EvmExceptions++;
                            return CallResult.StaticCallViolationException;
                        }

                        // TODO: happens in CREATE_empty000CreateInitCode_Transaction but probably has to be handled differently
                        if (!_state.AccountExists(env.ExecutingAccount))
                        {
                            _state.CreateAccount(env.ExecutingAccount, UInt256.Zero);
                        }

                        PopUInt256(out UInt256 value, bytesOnStack);
                        PopUInt256(out UInt256 memoryPositionOfInitCode, bytesOnStack);
                        PopUInt256(out UInt256 initCodeLength, bytesOnStack);

                        TaintInfo valueTaint = taintStack.Pop();
                        taintStack.Pop();
                        taintStack.Pop();

                        if (isTestingTarget && instruction == Instruction.CREATE && value > 0)
                        {
                            // ILF checks whether block state affects the ether to send or affects conditional branches.
                            if (valueTaint.IsBlockStateILF || BugOracle.FlowAffectedByBlockStateILF)
                            {
                                BugSet.Add((BugClass.BlockstateDependencyILF, programCounter - 1));
                            }
                        }

                        Span<byte> salt = null;
                        if (instruction == Instruction.CREATE2)
                        {
                            salt = PopBytes(bytesOnStack);
                            taintStack.Pop();
                        }

                        CheckStackConsistency("CREATE* (1)");

                        long gasCost = GasCostOf.Create + (instruction == Instruction.CREATE2 ? GasCostOf.Sha3Word * EvmPooledMemory.Div32Ceiling(initCodeLength) : 0);
                        if (!UpdateGas(gasCost, ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        UpdateMemoryCost(ref memoryPositionOfInitCode, initCodeLength);

                        // TODO: copy pasted from CALL / DELEGATECALL, need to move it outside?
                        if (env.CallDepth >= MaxCallDepth) // TODO: fragile ordering / potential vulnerability for different clients
                        {
                            // TODO: need a test for this
                            _returnDataBuffer = new byte[0];
                            PushZero(bytesOnStack);
                            PushNonTainted();
                            CheckStackConsistency("CREATE* (2)");
                            break;
                        }

                        Span<byte> initCode = evmState.Memory.LoadSpan(ref memoryPositionOfInitCode, initCodeLength);
                        UInt256 balance = _state.GetBalance(env.ExecutingAccount);
                        if (value > balance)
                        {
                            PushZero(bytesOnStack);
                            PushNonTainted();
                            CheckStackConsistency("CREATE* (3)");
                            break;
                        }

                        EndInstructionTrace();
                        // todo: === below is a new call - refactor / move

                        long callGas = spec.IsEip150Enabled ? gasAvailable - gasAvailable / 64L : gasAvailable;
                        if (!UpdateGas(callGas, ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        Address contractAddress = instruction == Instruction.CREATE
                            ? Address.OfContract(env.ExecutingAccount, _state.GetNonce(env.ExecutingAccount))
                            : Address.OfContract(env.ExecutingAccount, salt, initCode);

                        _state.IncrementNonce(env.ExecutingAccount);

                        int stateSnapshot = _state.TakeSnapshot();
                        int storageSnapshot = _storage.TakeSnapshot();

                        bool accountExists = _state.AccountExists(contractAddress);
                        if (accountExists && ((GetCachedCodeInfo(contractAddress)?.MachineCode?.Length ?? 0) != 0 || _state.GetNonce(contractAddress) != 0))
                        {
                            /* we get the snapshot before this as there is a possibility with that we will touch an empty account and remove it even if the REVERT operation follows */
                            if (isTrace) _logger.Trace($"Contract collision at {contractAddress}");
                            PushZero(bytesOnStack);
                            PushNonTainted();
                            CheckStackConsistency("CREATE* (4)");
                            break;
                        }

                        if (accountExists)
                        {
                            _state.UpdateStorageRoot(contractAddress, Keccak.EmptyTreeHash);
                        }

                        _state.SubtractFromBalance(env.ExecutingAccount, value, spec);
                        ExecutionEnvironment callEnv = new ExecutionEnvironment();
                        callEnv.TransferValue = value;
                        callEnv.Value = value;
                        callEnv.Sender = env.ExecutingAccount;
                        callEnv.CodeSource = null;
                        callEnv.Originator = env.Originator;
                        callEnv.CallDepth = env.CallDepth + 1;
                        callEnv.CurrentBlock = env.CurrentBlock;
                        callEnv.GasPrice = env.GasPrice;
                        callEnv.ExecutingAccount = contractAddress;
                        callEnv.CodeInfo = new CodeInfo(initCode.ToArray());
                        callEnv.InputData = Bytes.Empty;
                        EvmState callState = new EvmState(
                            callGas,
                            callEnv,
                            ExecutionType.Create,
                            false,
                            false,
                            stateSnapshot,
                            storageSnapshot,
                            0L,
                            0L,
                            evmState.IsStatic,
                            false);

                        UpdateCurrentState();
                        return new CallResult(callState);
                    }
                    case Instruction.RETURN:
                    {
                        if (isTestingTarget)
                        {
                            CheckMishandledExceptionMythril();
                        }
                        PopUInt256(out UInt256 memoryPos, bytesOnStack);
                        PopUInt256(out UInt256 length, bytesOnStack);

                        taintStack.Pop();
                        taintStack.Pop();
                        CheckStackConsistency("RETURN");

                        UpdateMemoryCost(ref memoryPos, length);
                        byte[] returnData = evmState.Memory.Load(ref memoryPos, length);

                        if (isTestingTarget)
                        {
                            // Mythril and Manticore raises alarms if overflows value is used in RETURN.
                            // Smartian does not, since we have not yet witnessed any real-world CVE where
                            // such strategy is needed.
                            HashSet<int> accOvf = new HashSet<int>();
                            for (UInt256 i = 0; i < length; i++)
                            {
                                if (taintMemory.ContainsKey(memoryPos + i))
                                {
                                  accOvf.UnionWith(taintMemory[memoryPos + i].OvfSrcs);
                                }
                            }
                            foreach (int pc in accOvf)
                            {
                                BugSet.Add((BugClass.IntegerBugMythril, pc));
                                BugSet.Add((BugClass.IntegerBugManticore, pc));
                            }
                        }

                        UpdateCurrentState();
                        EndInstructionTrace();
                        return new CallResult(returnData, null);
                    }
                    case Instruction.CALL:
                    case Instruction.CALLCODE:
                    case Instruction.DELEGATECALL:
                    case Instruction.STATICCALL:
                    {
                        Metrics.Calls++;

                        if (instruction == Instruction.DELEGATECALL && !spec.IsEip7Enabled ||
                            instruction == Instruction.STATICCALL && !spec.IsEip214Enabled)
                        {
                            Metrics.EvmExceptions++;
                            EndInstructionTraceError(BadInstructionErrorText);
                            return CallResult.InvalidInstructionException;
                        }

                        PopUInt(out BigInteger gasLimit, bytesOnStack);
                        taintStack.Pop();

                        Address codeSource = PopAddress(bytesOnStack);
                        TaintInfo callDstTaint = taintStack.Pop();
                        BugOracle.AddVarsUsedForCall(callDstTaint.VarSrcs, codeSource);

                        UInt256 callValue;
                        TaintInfo callValueTaint = TaintInfo.Bot();
                        HashSet<int> callValueOvf = new HashSet<int>();

                        switch (instruction)
                        {
                            case Instruction.STATICCALL:
                                callValue = UInt256.Zero;
                                break;
                            case Instruction.DELEGATECALL:
                                callValue = env.Value;
                                break;
                            default:
                                PopUInt256(out callValue, bytesOnStack);
                                callValueTaint = taintStack.Pop();
                                callValueOvf.UnionWith(callValueTaint.OvfSrcs);
                                BugOracle.AddVarsUsedForCall(callValueTaint.VarSrcs, codeSource);
                                break;
                        }

                        UInt256 transferValue = instruction == Instruction.DELEGATECALL ? UInt256.Zero : callValue;
                        PopUInt256(out UInt256 dataOffset, bytesOnStack);
                        PopUInt256(out UInt256 dataLength, bytesOnStack);
                        PopUInt256(out UInt256 outputOffset, bytesOnStack);
                        PopUInt256(out UInt256 outputLength, bytesOnStack);

                        taintStack.Pop();
                        taintStack.Pop();
                        taintStack.Pop();
                        taintStack.Pop();
                        CheckStackConsistency("*CALL (1)");

                        if (evmState.IsStatic && !transferValue.IsZero && instruction != Instruction.CALLCODE)
                        {
                            Metrics.EvmExceptions++;
                            return CallResult.StaticCallViolationException;
                        }

                        bool isPrecompile = codeSource.IsPrecompiled(spec);
                        Address sender = instruction == Instruction.DELEGATECALL ? env.Sender : env.ExecutingAccount;
                        Address target = instruction == Instruction.CALL || instruction == Instruction.STATICCALL ? codeSource : env.ExecutingAccount;

                        if (isTrace)
                        {
                            _logger.Trace($"Tx sender {sender}");
                            _logger.Trace($"Tx code source {codeSource}");
                            _logger.Trace($"Tx target {target}");
                            _logger.Trace($"Tx value {callValue}");
                            _logger.Trace($"Tx transfer value {transferValue}");
                        }

                        if (isTestingTarget)
                        {
                            if (instruction == Instruction.DELEGATECALL)
                            {
                                BugOracle.UseDelegateCall = true;
                            }

                            if (callValue > 0) // Ether send takes place.
                            {
                                BugOracle.SendEther = true;
                                BugOracle.LastEtherSendPC = programCounter - 1;
                                if (instruction == Instruction.CALL)
                                {
                                    BugOracle.SendEtherIndependently = true;
                                }

                                // We maintain send flag for each call depth, to prevent mistaking RE as MS.
                                if (BugOracle.DepthsWithSend.Contains(env.CallDepth))
                                {
                                    BugSet.Add((BugClass.MultipleSend, programCounter - 1));
                                }
                                BugOracle.DepthsWithSend.Add(env.CallDepth);
                            }

                            // Raise IB alarms if overflowed value decides the amount of ether to send.
                            foreach (int pc in callValueOvf)
                            {
                                BugSet.Add((BugClass.IntegerBug, pc));
                                BugSet.Add((BugClass.IntegerBugMythril, pc));
                                // Note that Manticore does not consider CALL as a sink.
                            }

                            if (instruction == Instruction.DELEGATECALL)
                            {
                                // Check whether an attacker can set the destination into one of the attacker's contract.
                                if (!HadDeployerTx && IsUser(codeSource))
                                {
                                    BugSet.Add((BugClass.ControlHijack, programCounter - 1));
                                }
                            }

                            if (instruction == Instruction.CALL)
                            {
                                // As a part of reentrancy detection, first check for the occurence of a cyclic call.
                                if (BugOracle.SendEther && BugOracle.CalledAddrs.Contains(codeSource) && env.CallDepth >= 3)
                                {
                                    BugOracle.CyclicCallDsts.Add(codeSource);
                                }
                                BugOracle.CalledAddrs.Add(codeSource);
                            }

                            // ILF records the PC of (the latest) send, and compares PCs later.
                            if (instruction == Instruction.CALL && gasLimit > 0 && callValue > 0)
                            {
                                BugOracle.LastSendPC = programCounter - 1;
                            }

                            // sFuzz checks TX depth for cyclic call.
                            if (env.CallDepth + 1 >= 4)
                            {
                                BugOracle.CyclicCallPCs.Add(programCounter - 1);
                            }

                            // Mythril checks the gaslimit and whether the destination contract is controllable.
                            if (instruction == Instruction.CALL && gasLimit > 2300 && IsUser(codeSource))
                            {
                                BugSet.Add((BugClass.ReentrancyMythril, programCounter - 1));
                            }

                            // Manticore also checks the gaslimit and whether the destination contract is controllable.
                            // In addition, it also compares the destination address with the TX sender.
                            if (instruction == Instruction.CALL && gasLimit > 2300 && (IsUser(codeSource) || codeSource == env.Sender))
                            {
                                BugOracle.HadExternCall = true;
                            }

                            // Raise a BD alarm if ether send is directly or indirectly affected by the block state.
                            if (instruction == Instruction.CALL && callValue > 0)
                            {
                                if (callDstTaint.IsBlockState || callValueTaint.IsBlockState || BugOracle.FlowAffectedByBlockState)
                                {
                                    BugSet.Add((BugClass.BlockstateDependency, programCounter - 1));
                                }
                            }

                            // ILF checks whether block state affects the ether to send or affects conditional branches.
                            if ((instruction == Instruction.CALL || instruction == Instruction.CALLCODE) && callValue > 0)
                            {
                                if (callValueTaint.IsBlockStateILF || BugOracle.FlowAffectedByBlockStateILF)
                                {
                                    BugSet.Add((BugClass.BlockstateDependencyILF, programCounter - 1));
                                }
                            }
                        }

                        long gasExtra = 0L;

                        if (!transferValue.IsZero)
                        {
                            gasExtra += GasCostOf.CallValue;
                        }

                        if (!spec.IsEip158Enabled && !_state.AccountExists(target))
                        {
                            gasExtra += GasCostOf.NewAccount;
                        }

                        if (spec.IsEip158Enabled && transferValue != 0 && _state.IsDeadAccount(target))
                        {
                            gasExtra += GasCostOf.NewAccount;
                        }

                        if (!UpdateGas(spec.IsEip150Enabled ? GasCostOf.CallEip150 : GasCostOf.Call, ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        UpdateMemoryCost(ref dataOffset, dataLength);
                        UpdateMemoryCost(ref outputOffset, outputLength);
                        if (!UpdateGas(gasExtra, ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        if (spec.IsEip150Enabled)
                        {
                            gasLimit = BigInteger.Min(gasAvailable - gasAvailable / 64L, gasLimit);
                        }

                        long gasLimitUl = (long)gasLimit;
                        if (!UpdateGas(gasLimitUl, ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        if (!transferValue.IsZero)
                        {
                            gasLimitUl += GasCostOf.CallStipend;
                        }

                        if (env.CallDepth >= MaxCallDepth || !transferValue.IsZero && _state.GetBalance(env.ExecutingAccount) < transferValue)
                        {
                            _returnDataBuffer = new byte[0];
                            PushZero(bytesOnStack);

                            PushNonTainted();
                            CheckStackConsistency("*CALL* (2)");

                            if (_txTracer.IsTracingInstructions)
                            {
                                // very specific for Parity trace, need to find generalization - very peculiar 32 length...
                                byte[] memoryTrace = evmState.Memory.Load(ref dataOffset, 32);
                                _txTracer.ReportMemoryChange((long)dataOffset, memoryTrace);
                            }

                            if (isTrace) _logger.Trace("FAIL - call depth");
                            if(_txTracer.IsTracingInstructions) _txTracer.ReportOperationRemainingGas(gasAvailable);
                            if(_txTracer.IsTracingInstructions) _txTracer.ReportOperationError(EvmExceptionType.NotEnoughBalance);

                            RefundGas(gasLimitUl, ref gasAvailable);
                            if(_txTracer.IsTracingInstructions) _txTracer.ReportRefundForVmTrace(gasLimitUl, gasAvailable);
                            break;
                        }

                        byte[] callData = evmState.Memory.Load(ref dataOffset, dataLength);

                        int stateSnapshot = _state.TakeSnapshot();
                        int storageSnapshot = _storage.TakeSnapshot();
                        _state.SubtractFromBalance(sender, transferValue, spec);

                        ExecutionEnvironment callEnv = new ExecutionEnvironment();
                        callEnv.CallDepth = env.CallDepth + 1;
                        callEnv.CurrentBlock = env.CurrentBlock;
                        callEnv.GasPrice = env.GasPrice;
                        callEnv.Originator = env.Originator;
                        callEnv.Sender = sender;
                        callEnv.CodeSource = codeSource;
                        callEnv.ExecutingAccount = target;
                        callEnv.TransferValue = transferValue;
                        callEnv.Value = callValue;
                        callEnv.InputData = callData;
                        callEnv.CodeInfo = isPrecompile ? new CodeInfo(codeSource) : GetCachedCodeInfo(codeSource);

                        if (isTrace) _logger.Trace($"Tx call gas {gasLimitUl}");
                        if (outputLength == 0)
                        {
                            // TODO: when output length is 0 outputOffset can have any value really
                            // and the value does not matter and it can cause trouble when beyond long range
                            outputOffset = 0;
                        }

                        ExecutionType executionType;
                        if (instruction == Instruction.CALL)
                        {
                            executionType = ExecutionType.Call;
                        }
                        else if (instruction == Instruction.DELEGATECALL)
                        {
                            executionType = ExecutionType.DelegateCall;
                        }
                        else if (instruction == Instruction.STATICCALL)
                        {
                            executionType = ExecutionType.StaticCall;
                        }
                        else if (instruction == Instruction.CALLCODE)
                        {
                            executionType = ExecutionType.CallCode;
                        }
                        else
                        {
                            throw new NotImplementedException($"Execution type is undefined for {Enum.GetName(typeof(Instruction), instruction)}");
                        }

                        EvmState callState = new EvmState(
                            gasLimitUl,
                            callEnv,
                            executionType,
                            isPrecompile,
                            false,
                            stateSnapshot,
                            storageSnapshot,
                            (long)outputOffset,
                            (long)outputLength,
                            instruction == Instruction.STATICCALL || evmState.IsStatic,
                            false);

                        UpdateCurrentState();
                        EndInstructionTrace();
                        return new CallResult(callState);
                    }
                    case Instruction.REVERT:
                    {
                        if (!spec.IsEip140Enabled)
                        {
                            Metrics.EvmExceptions++;
                            EndInstructionTraceError(BadInstructionErrorText);
                            return CallResult.InvalidInstructionException;
                        }

                        PopUInt256(out UInt256 memoryPos, bytesOnStack);
                        PopUInt256(out UInt256 length, bytesOnStack);

                        taintStack.Pop();
                        taintStack.Pop();
                        CheckStackConsistency("REVERT");

                        UpdateMemoryCost(ref memoryPos, length);
                        byte[] errorDetails = evmState.Memory.Load(ref memoryPos, length);

                        if (isTestingTarget)
                        {
                            BugSet.Add((BugClass.RequirementViolation, programCounter - 1));
                        }

                        UpdateCurrentState();
                        EndInstructionTrace();
                        return new CallResult(errorDetails, null, true);
                    }
                    case Instruction.INVALID:
                    {
                        if (!UpdateGas(GasCostOf.High, ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        if (isTestingTarget)
                        {
                            BugSet.Add((BugClass.AssertionFailure, programCounter - 1));
                        }

                        Metrics.EvmExceptions++;
                        EndInstructionTraceError(BadInstructionErrorText);
                        return CallResult.InvalidInstructionException;
                    }
                    case Instruction.SELFDESTRUCT:
                    {
                        if (evmState.IsStatic)
                        {
                            Metrics.EvmExceptions++;
                            return CallResult.StaticCallViolationException;
                        }

                        if (spec.IsEip150Enabled && !UpdateGas(GasCostOf.SelfDestructEip150, ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        Metrics.SelfDestructs++;

                        Address inheritor = PopAddress(bytesOnStack);

                        taintStack.Pop();
                        CheckStackConsistency("SELFDESTRUCT");

                        evmState.DestroyList.Add(env.ExecutingAccount);
                        _storage.Destroy(env.ExecutingAccount);

                        UInt256 ownerBalance = _state.GetBalance(env.ExecutingAccount);
                        if(_txTracer.IsTracingActions) _txTracer.ReportSelfDestruct(env.ExecutingAccount, ownerBalance, inheritor);
                        if (spec.IsEip158Enabled && ownerBalance != 0 && _state.IsDeadAccount(inheritor))
                        {
                            if (!UpdateGas(GasCostOf.NewAccount, ref gasAvailable))
                            {
                                EndInstructionTraceError(OutOfGasErrorText);
                                return CallResult.OutOfGasException;
                            }
                        }

                        bool inheritorAccountExists = _state.AccountExists(inheritor);
                        if (!spec.IsEip158Enabled && !inheritorAccountExists && spec.IsEip150Enabled)
                        {
                            if (!UpdateGas(GasCostOf.NewAccount, ref gasAvailable))
                            {
                                EndInstructionTraceError(OutOfGasErrorText);
                                return CallResult.OutOfGasException;
                            }
                        }

                        if (!inheritorAccountExists)
                        {
                            _state.CreateAccount(inheritor, ownerBalance);
                        }
                        else if (!inheritor.Equals(env.ExecutingAccount))
                        {
                            _state.AddToBalance(inheritor, ownerBalance, spec);
                        }

                        _state.SubtractFromBalance(env.ExecutingAccount, ownerBalance, spec);

                        if (isTestingTarget)
                        {
                            BugOracle.SendEtherIndependently = true;
                            // If there was any transaction from deployer, ownership could have been trasnferred.
                            if (!HadDeployerTx && IsUser(inheritor))
                            {
                                BugSet.Add((BugClass.SuicidalContract, programCounter - 1));
                            }
                        }

                        UpdateCurrentState();
                        EndInstructionTrace();
                        return CallResult.Empty;
                    }
                    case Instruction.SHL:
                    {
                        if (!spec.IsEip145Enabled)
                        {
                            Metrics.EvmExceptions++;
                            EndInstructionTraceError(BadInstructionErrorText);
                            return CallResult.InvalidInstructionException;
                        }

                        if (!UpdateGas(GasCostOf.VeryLow, ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        PopUInt256(out UInt256 a, bytesOnStack);
                        if (a >= 256UL)
                        {
                            PopLimbo();
                            PushZero(bytesOnStack);
                        }
                        else
                        {
                            PopUInt256(out UInt256 b, bytesOnStack);
                            BigInteger res = b << (int) a.S0;
                            PushSignedInt(ref res, bytesOnStack);
                        }

                        BinOpTaintStack();
                        CheckStackConsistency("SHL");

                        break;
                    }
                    case Instruction.SHR:
                    {
                        if (!spec.IsEip145Enabled)
                        {
                            Metrics.EvmExceptions++;
                            EndInstructionTraceError(BadInstructionErrorText);
                            return CallResult.InvalidInstructionException;
                        }

                        if (!UpdateGas(GasCostOf.VeryLow, ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        PopUInt256(out UInt256 a, bytesOnStack);
                        if (a >= 256)
                        {
                            PopLimbo();
                            PushZero(bytesOnStack);
                        }
                        else
                        {
                            PopUInt256(out UInt256 b, bytesOnStack);
                            UInt256 res = b >> (int) a.S0;
                            PushUInt256(ref res, bytesOnStack);
                        }

                        BinOpTaintStack();
                        CheckStackConsistency("SHR");

                        break;
                    }
                    case Instruction.SAR:
                    {
                        if (!spec.IsEip145Enabled)
                        {
                            Metrics.EvmExceptions++;
                            EndInstructionTraceError(BadInstructionErrorText);
                            return CallResult.InvalidInstructionException;
                        }

                        if (!UpdateGas(GasCostOf.VeryLow, ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        PopUInt(out BigInteger a, bytesOnStack);
                        PopInt(out BigInteger b, bytesOnStack);
                        if (a >= BigInt256)
                        {
                            if (b.Sign >= 0)
                            {
                                PushZero(bytesOnStack);
                            }
                            else
                            {
                                BigInteger res = BigInteger.MinusOne;
                                PushSignedInt(ref res, bytesOnStack);
                            }
                        }
                        else
                        {
                            BigInteger res = BigInteger.DivRem(b, BigInteger.Pow(2, (int)a), out BigInteger remainder);
                            if (remainder.Sign < 0)
                            {
                                res--;
                            }

                            PushSignedInt(ref res, bytesOnStack);
                        }

                        BinOpTaintStack();
                        CheckStackConsistency("SAR");

                        break;
                    }
                    case Instruction.EXTCODEHASH:
                    {
                        if (!spec.IsEip1052Enabled)
                        {
                            Metrics.EvmExceptions++;
                            EndInstructionTraceError(BadInstructionErrorText);
                            return CallResult.InvalidInstructionException;
                        }

                        var gasCost = spec.IsEip1884Enabled ? GasCostOf.ExtCodeHashEip1884 : GasCostOf.ExtCodeHash;
                        if (!UpdateGas(gasCost, ref gasAvailable))
                        {
                            EndInstructionTraceError(OutOfGasErrorText);
                            return CallResult.OutOfGasException;
                        }

                        Address address = PopAddress(bytesOnStack);
                        if (!_state.AccountExists(address) || _state.IsDeadAccount(address))
                        {
                            PushZero(bytesOnStack);
                        }
                        else
                        {
                            PushBytes(_state.GetCodeHash(address).Bytes, bytesOnStack);
                        }

                        taintStack.Pop();
                        PushNonTainted();
                        CheckStackConsistency("EXTCODEHASH");

                        break;
                    }
                    default:
                    {
                        Metrics.EvmExceptions++;
                        EndInstructionTraceError(BadInstructionErrorText);
                        return CallResult.InvalidInstructionException;
                    }
                }

                EndInstructionTrace();
            }

            UpdateCurrentState();
            return CallResult.Empty;
        }

        internal struct CallResult
        {
            public static CallResult OutOfGasException = new CallResult(EvmExceptionType.OutOfGas);
            public static CallResult AccessViolationException = new CallResult(EvmExceptionType.AccessViolation);
            public static CallResult InvalidJumpDestination = new CallResult(EvmExceptionType.InvalidJumpDestination);
            public static CallResult InvalidInstructionException = new CallResult(EvmExceptionType.BadInstruction);
            public static CallResult StaticCallViolationException = new CallResult(EvmExceptionType.StaticCallViolation);
            public static CallResult StackOverflowException = new CallResult(EvmExceptionType.StackOverflow); // TODO: use these to avoid CALL POP attacks
            public static CallResult StackUnderflowException = new CallResult(EvmExceptionType.StackUnderflow); // TODO: use these to avoid CALL POP attacks
            public static readonly CallResult Empty = new CallResult(Bytes.Empty, null);

            public CallResult(EvmState stateToExecute)
            {
                StateToExecute = stateToExecute;
                Output = Bytes.Empty;
                PrecompileSuccess = null;
                ShouldRevert = false;
                ExceptionType = EvmExceptionType.None;
            }

            private CallResult(EvmExceptionType exceptionType)
            {
                StateToExecute = null;
                Output = StatusCode.FailureBytes;
                PrecompileSuccess = null;
                ShouldRevert = false;
                ExceptionType = exceptionType;
            }

            public CallResult(byte[] output, bool? precompileSuccess, bool shouldRevert = false, EvmExceptionType exceptionType = EvmExceptionType.None)
            {
                StateToExecute = null;
                Output = output;
                PrecompileSuccess = precompileSuccess;
                ShouldRevert = shouldRevert;
                ExceptionType = exceptionType;
            }

            public EvmState StateToExecute { get; }
            public byte[] Output { get; }
            public EvmExceptionType ExceptionType { get; }
            public bool ShouldRevert { get; }
            public bool? PrecompileSuccess { get; } // TODO: check this behaviour as it seems it is required and previously that was not the case
            public bool IsReturn => StateToExecute == null;
            public bool IsException => ExceptionType != EvmExceptionType.None;
        }
    }
}