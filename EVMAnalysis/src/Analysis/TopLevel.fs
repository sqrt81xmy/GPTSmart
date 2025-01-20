module EVMAnalysis.TopLevel

open EVMAnalysis
open System.IO 

type Sequence = string list

let private analyzeConstructor cfgs constrFunc =
  let constrInfo = AbstractInterpret.run cfgs Set.empty constrFunc
  let constrTainted = constrInfo.ConstrTainted
  let taintStr = Set.map Variable.toString constrTainted |> String.concat ", "
  FuncInfo.print constrInfo // DEBUG
  printfn "Constructor tainted: { %s }" taintStr // DEBUG
  constrTainted

let private analyzeNormalFuncs cfgs constrTainted funcs =
  let mapper func =
    let funcInfo = AbstractInterpret.run cfgs constrTainted func
    FuncInfo.print funcInfo // DEBUG
    funcInfo
  List.map mapper funcs

let private initializeWorkList funcInfos =
  let defs = List.filter (fun i -> not (Set.isEmpty i.Defs)) funcInfos
  let defOnlys, defAndUses = List.partition (fun i -> Set.isEmpty i.Uses) defs
  (defOnlys @ defAndUses)
  |> List.map (fun fInfo -> FuncSpec.getName fInfo.FuncSpec)
  |> List.map (fun fName -> [fName])

let private evalDUChain funcInfoMap (funcSeq: Sequence): Set<DUChain> =
  let folder (accChains, accDefMap) f =
    let funcInfo = Map.find f funcInfoMap
    let defs = funcInfo.Defs
    let uses = funcInfo.Uses
    let chooser useVar =
      match Map.tryFind useVar accDefMap with
      | None -> None
      | Some defFunc -> Some (defFunc, useVar, f)
    let accChains = Set.union accChains (Set.choose chooser uses)
    // Approximate that 'f' always updates 'defs', to avoid too long sequence.
    let folder acc defVar = Map.add defVar f acc
    let accDefMap = Set.fold folder accDefMap defs
    (accChains, accDefMap)
  List.fold folder (Set.empty, Map.empty) funcSeq |> fst

let private checkDUChainGain funcInfoMap chains seqs =
  let folder (accChains, accPromising) seq =
    let duChains = evalDUChain funcInfoMap seq
    if Set.isEmpty (Set.difference duChains accChains)
    then (accChains, accPromising)
    else (Set.union accChains duChains, seq :: accPromising)
  List.fold folder (chains, []) seqs

// Tests if s1 is a prefix of s2.
let rec private isPrefix s1 s2 =
  match s1, s2 with
  | [], _ -> true
  | _, [] -> false
  | h1 :: t1, h2 :: t2 -> if h1 = h2 then isPrefix t1 t2 else false

// Tests if s1 is a sub-sequence of s2.
let rec private isSubSeq s1 s2 =
  match s2 with
  | [] -> false
  | _ :: t2 -> if isPrefix s1 s2 then true else isSubSeq s1 t2

let rec private pruneWorkList = function
  | [] -> []
  | headSeq :: tailSeqs ->
    if List.exists (fun s -> isSubSeq headSeq s) tailSeqs then
      printfn "Pruning out %A" headSeq
      pruneWorkList tailSeqs // Drop headSeq.
    else
      let filter tailSeq =
        if isSubSeq tailSeq headSeq then printfn "Pruning out %A" tailSeq; false
        else true
      headSeq :: pruneWorkList (List.filter filter tailSeqs)

let rec private buildLoop funcInfoMap (accChains, accSeqs) works =
  match works with
  | [] -> accSeqs
  | candidate :: tailWorks ->
    let allFuncNames = Map.keys funcInfoMap
    let appends = List.map (fun f -> candidate @ [f]) allFuncNames
    let accChains, promisings = checkDUChainGain funcInfoMap accChains appends
    let accSeqs = if not (List.isEmpty promisings) then accSeqs
                  else candidate :: accSeqs // Add if no more room to improve.
    let newWorks = pruneWorkList (promisings @ tailWorks)
    buildLoop funcInfoMap (accChains, accSeqs) newWorks

let parseOnly binFile abiFile =
  let _, _, constrFunc, normalFuncs = Parse.run binFile abiFile
  ContractSpec.make constrFunc (Array.ofList normalFuncs)

let writeNormalFuncsToFile path (funcSpecs: FuncSpec list) =
    printfn "lailelaile"
    // 将 normalFuncs 转换为字符串
    if not (File.Exists(path)) then
        // 如果文件不存在，创建它
      let fileStream = File.Create(path) // 创建文件并打开流
      printfn "create File"
      fileStream.Close() // 关闭文件流
    let arraySpecs = Array.ofList funcSpecs
    File.WriteAllLines(path, arraySpecs |> Array.map (fun fs -> sprintf "%A" fs))

// 将 FuncSpec 转换为字符串的函数
let funcSpecToString (spec: FuncSpec) : string =
    sprintf "%A" spec

// 修改 appendToFile 函数以接收 FuncSpec 类型
let appendToFile (filePath: string) (content: FuncSpec) =
    // 将 FuncSpec 转换为字符串后写入
    let contentString = funcSpecToString content
    use writer = new StreamWriter(filePath, true) // 以追加模式打开文件
    writer.WriteLine(contentString) // 写入内容

let parseAndAnalyze binFile abiFile =
  // Parse and statically analyze bytecode.
  let preCFGs, postCFGs, constrFunc, normalFuncs = Parse.run binFile abiFile
  // 假设 normalFuncs 是一个包含函数信息的数组或列表


  printfn "Normal functions have been written to %A  " constrFunc

  let constrTainted = analyzeConstructor preCFGs constrFunc
  let funcInfos = analyzeNormalFuncs postCFGs constrTainted normalFuncs
  // Next, generate ContractSpec to return. Should recompute 'normalFuncs' by
  // extracting from 'funcInfos', to reflect the updates from static analysis.
  let normalFuncs = List.map (fun info -> info.FuncSpec) funcInfos
  let contractSpec = ContractSpec.make constrFunc (Array.ofList normalFuncs)
  // printfn "contractSpec %A" contractSpec
  // Now, decide transaction sequence order with the analysis result.
  let folder accMap info = Map.add (FuncSpec.getName info.FuncSpec) info accMap
  let funcInfoMap = List.fold folder Map.empty funcInfos

  let initWorks = initializeWorkList funcInfos
  let seqs = buildLoop funcInfoMap (Set.empty, []) initWorks
  printfn "(%d candidate sequences)" (List.length seqs)
  List.iter (fun seq -> printfn "%A" seq) seqs
 
  (contractSpec, seqs)
