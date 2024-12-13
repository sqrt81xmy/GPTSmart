namespace Nethermind.Evm {

    public enum BugClass
    {
        AssertionFailure,
        ArbitraryWrite,
        BlockstateDependency,
        BlockstateDependencySFuzz,
        BlockstateDependencyILF,
        BlockstateDependencyMythril,
        BlockstateDependencyManticore,
        ControlHijack,
        EtherLeak,
        IntegerBug,
        IntegerBugSFuzz,
        IntegerBugMythril,
        IntegerBugManticore,
        MishandledException,
        MishandledExceptionSFuzz,
        MishandledExceptionILF,
        MishandledExceptionMythril,
        MishandledExceptionManticore,
        MultipleSend,
        Reentrancy,
        ReentrancySFuzz,
        ReentrancyILF,
        ReentrancyMythril,
        ReentrancyManticore,
        SuicidalContract,
        TransactionOriginUse,
        FreezingEther,
        RequirementViolation
    }

    public class BugClassHelper {
        public static string toString(BugClass bug) {
            return bug.ToString();
        }

        public static bool isOptional(BugClass bug) {
            switch (bug) {
                case BugClass.FreezingEther:
                case BugClass.RequirementViolation:
                    return true;
                default:
                    return false;
            }
        }

        public static bool isFromOtherTools(BugClass bug) {
            switch (bug) {
                case BugClass.AssertionFailure:
                case BugClass.ArbitraryWrite:
                case BugClass.BlockstateDependency:
                case BugClass.ControlHijack:
                case BugClass.EtherLeak:
                case BugClass.FreezingEther:
                case BugClass.IntegerBug:
                case BugClass.MishandledException:
                case BugClass.MultipleSend:
                case BugClass.Reentrancy:
                case BugClass.RequirementViolation:
                case BugClass.SuicidalContract:
                case BugClass.TransactionOriginUse:
                    return false;

                case BugClass.BlockstateDependencySFuzz:
                case BugClass.BlockstateDependencyILF:
                case BugClass.BlockstateDependencyMythril:
                case BugClass.BlockstateDependencyManticore:
                case BugClass.IntegerBugSFuzz:
                case BugClass.IntegerBugMythril:
                case BugClass.IntegerBugManticore:
                case BugClass.MishandledExceptionSFuzz:
                case BugClass.MishandledExceptionILF:
                case BugClass.MishandledExceptionMythril:
                case BugClass.MishandledExceptionManticore:
                case BugClass.ReentrancySFuzz:
                case BugClass.ReentrancyILF:
                case BugClass.ReentrancyMythril:
                case BugClass.ReentrancyManticore:
                    return true;

                default:
                    return false; // Must be unreachable.
            }
        }

        public static string toTag(BugClass bug) {
            switch (bug) {
                case BugClass.AssertionFailure:
                    return "AF";
                case BugClass.ArbitraryWrite:
                    return "AW";
                case BugClass.BlockstateDependency:
                    return "BD";
                case BugClass.BlockstateDependencySFuzz:
                    return "BD_sfuzz";
                case BugClass.BlockstateDependencyILF:
                    return "BD_ilf";
                case BugClass.BlockstateDependencyMythril:
                    return "BD_myth";
                case BugClass.BlockstateDependencyManticore:
                    return "BD_mant";
                case BugClass.ControlHijack:
                    return "CH";
                case BugClass.EtherLeak:
                    return "EL";
                case BugClass.IntegerBug:
                    return "IB";
                case BugClass.IntegerBugSFuzz:
                    return "IB_sfuzz";
                case BugClass.IntegerBugMythril:
                    return "IB_myth";
                case BugClass.IntegerBugManticore:
                    return "IB_mant";
                case BugClass.MishandledException:
                    return "ME";
                case BugClass.MishandledExceptionSFuzz:
                    return "ME_sfuzz";
                case BugClass.MishandledExceptionILF:
                    return "ME_ilf";
                case BugClass.MishandledExceptionMythril:
                    return "ME_myth";
                case BugClass.MishandledExceptionManticore:
                    return "ME_mant";
                case BugClass.MultipleSend:
                    return "MS";
                case BugClass.Reentrancy:
                    return "RE";
                case BugClass.ReentrancySFuzz:
                    return "RE_sfuzz";
                case BugClass.ReentrancyILF:
                    return "RE_ilf";
                case BugClass.ReentrancyMythril:
                    return "RE_myth";
                case BugClass.ReentrancyManticore:
                    return "RE_mant";
                case BugClass.SuicidalContract:
                    return "SC";
                case BugClass.TransactionOriginUse:
                    return "TO";
                case BugClass.FreezingEther:
                    return "FE";
                case BugClass.RequirementViolation:
                    return "RV";
                default:
                    return "unknown"; // Must be unreachable.
            }
        }
    }
}
