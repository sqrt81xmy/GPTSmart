using Nethermind.Dirichlet.Numerics;
using System.Collections.Generic;
using Nethermind.Core;

namespace Nethermind.Evm {

    public class BugOracle
    {
        // Block state dependency
        public bool FlowAffectedByBlockState { get; set; } = false; // Smartian
        public bool FlowAffectedByBlockStateILF { get; set; } = false; // ILF
        public HashSet<int> BlockStateInstrs = new HashSet<int>(); // sFuzz

        // Ether leak (auxiliary information for report)
        public int LastEtherSendPC { get; set; } = 0;

        // Freezing ether
        public bool UseDelegateCall { get; set; } = false;
        public bool SendEtherIndependently { get; set; } = false;

        // Mishandled exception
        public HashSet<int> ExceptionReturns = new HashSet<int>(); // Smartian, Mythril, Manticore
        public bool TopLevelException { get; set; } = false; // ILF, sFuzz
        public bool NonTopLevelException { get; set; } = false; // ILF, sFuzz
        public HashSet<int> UncheckedReturns = new HashSet<int>(); // ILF, sFuzz

        // Multiple send
        public HashSet<int> DepthsWithSend = new HashSet<int>();

        // Reentrancy
        public bool SendEther { get; set; } = false; // Shared
        public HashSet<Address> CalledAddrs = new HashSet<Address>(); // Smartian
        public HashSet<Address> CyclicCallDsts = new HashSet<Address>(); // Smartian
        public Dictionary<UInt256,HashSet<Address>> VarsUsedForCall = new Dictionary<UInt256, HashSet<Address>>(); // Smartian
        public HashSet<UInt256> VarsUsedForCond = new HashSet<UInt256>(); // Smartian
        public int LastSendPC = -1; // ILF
        public int LastSStorePC = -1; // ILF
        public HashSet<int>CyclicCallPCs = new HashSet<int>(); // sFuzz
        public bool HadExternCall = false; // Manticore

        public void AddVarsUsedForCall(HashSet<UInt256> vars, Address callAddr)
        {
            foreach (UInt256 varIdx in vars)
            {
                if (!VarsUsedForCall.ContainsKey(varIdx))
                {
                    VarsUsedForCall[varIdx] = new HashSet<Address>();
                }
                VarsUsedForCall[varIdx].Add(callAddr);
            }
        }

        public bool CheckAffectOnCyclicCall(UInt256 varIdx)
        {
            // Check if the given variable had been used in a conditional.
            if (VarsUsedForCond.Contains(varIdx) && CyclicCallDsts.Count > 0)
            {
                return true;
            }

            // Check if the given variable had been used in a cyclic call.
            if (VarsUsedForCall.ContainsKey(varIdx))
            {
                HashSet<Address> calls = new HashSet<Address>(VarsUsedForCall[varIdx]);
                calls.IntersectWith(CyclicCallDsts);
                return (calls.Count > 0);
            }

            return false;
        }

        public void ResetPerTx()
        {
            // Block state dependency
            FlowAffectedByBlockState = false;
            // Note that 'FlowAffectedByBlockStateILF' must not be reset.
            BlockStateInstrs.Clear();

            // Ether leak
            LastEtherSendPC = 0;

            // Freezing ether
            UseDelegateCall = false;
            SendEtherIndependently = false;

            // Mishandled exception
            TopLevelException = false;
            NonTopLevelException = false;
            ExceptionReturns.Clear();
            UncheckedReturns.Clear();

            // Multiple send
            DepthsWithSend.Clear();

            // Reentrancy
            SendEther = false;
            CalledAddrs.Clear();
            CyclicCallDsts.Clear();
            VarsUsedForCall.Clear();
            VarsUsedForCond.Clear();
            CyclicCallPCs.Clear();
            LastSendPC = -1;
            LastSStorePC = -1;
            HadExternCall = false;
        }
    }
}
