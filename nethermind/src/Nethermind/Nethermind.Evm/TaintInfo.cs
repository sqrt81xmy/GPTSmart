using System.Collections.Generic;
using Nethermind.Dirichlet.Numerics;
using Nethermind.Core;

namespace Nethermind.Evm
{
    public class TaintInfo
    {
        public bool IsBlockState;
        public bool IsBlockStateILF;
        public bool IsBlockStateMythril;
        public bool IsOrigin;
        public bool IsSender;
        public HashSet<int> ReturnSrcs;
        public HashSet<int> OvfSrcs;
        public HashSet<UInt256> VarSrcs;

        public TaintInfo() {
            IsBlockState = false;
            IsBlockStateILF = false;
            IsBlockStateMythril = false;
            IsOrigin = false;
            IsSender = false;
            ReturnSrcs = new HashSet<int>();
            OvfSrcs = new HashSet<int>();
            VarSrcs = new HashSet<UInt256>();
        }

        public TaintInfo(TaintInfo t) {
            IsBlockState = t.IsBlockState;
            IsBlockStateILF = t.IsBlockStateILF;
            IsBlockStateMythril = t.IsBlockStateMythril;
            IsOrigin = t.IsOrigin;
            IsSender = t.IsSender;
            ReturnSrcs = new HashSet<int>(t.ReturnSrcs);
            OvfSrcs = new HashSet<int>(t.OvfSrcs);
            VarSrcs = new HashSet<UInt256>(t.VarSrcs);
        }

        public void Join(TaintInfo t) {
            IsBlockState = IsBlockState || t.IsBlockState;
            IsBlockStateILF = IsBlockStateILF || t.IsBlockStateILF;
            IsBlockStateMythril = IsBlockStateMythril || t.IsBlockStateMythril;
            IsOrigin = IsOrigin || t.IsOrigin;
            IsSender = IsSender || t.IsSender;
            ReturnSrcs.UnionWith(t.ReturnSrcs);
            OvfSrcs.UnionWith(t.OvfSrcs);
            VarSrcs.UnionWith(t.VarSrcs);
        }

        // Join block state depdendency flags only.
        public void JoinDependency(TaintInfo t) {
            IsBlockState = IsBlockState || t.IsBlockState;
            IsBlockStateILF = IsBlockStateILF || t.IsBlockStateILF;
            IsBlockStateMythril = IsBlockStateMythril || t.IsBlockStateMythril;
        }

        public static TaintInfo Bot() {
            return new TaintInfo();
        }

        public static TaintInfo BlockState(Instruction ins, bool isOldBlock) {
            TaintInfo t = new TaintInfo();
            // (Instructions considered as taint source by each tool)
            // Smartian: TIMESTAMP / NUMBER / COINBASE / GASLIMIT/ DIFFICULTY / BLOACKHASH
            // ILF: TIMESTAMP / NUMBER / COINBASE / GASLIMIT / DIFFICULTY
            // Mythril: TIMESTAMP / NUMBER / COINBASE / GASLIMIT / BLOACKHASH (conditional)
            switch (ins) {
                case Instruction.TIMESTAMP:
                case Instruction.NUMBER:
                case Instruction.COINBASE:
                case Instruction.GASLIMIT:
                    t.IsBlockState = true;
                    t.IsBlockStateILF = true;
                    t.IsBlockStateMythril = true;
                    break;

                case Instruction.BLOCKHASH:
                    t.IsBlockState = true;
                    t.IsBlockStateMythril = isOldBlock;
                    break;

                case Instruction.DIFFICULTY:
                    t.IsBlockState = true;
                    t.IsBlockStateILF = true;
                    break;

                default:
                    break;
            }
            return t;
        }

        public static TaintInfo Origin() {
            TaintInfo t = new TaintInfo();
            t.IsOrigin = true;
            return t;
        }

        public static TaintInfo Sender() {
            TaintInfo t = new TaintInfo();
            t.IsSender = true;
            return t;
        }

        public static TaintInfo Return(int callPC) {
            TaintInfo t = new TaintInfo();
            t.ReturnSrcs.Add(callPC);
            return t;
        }

    }
}
