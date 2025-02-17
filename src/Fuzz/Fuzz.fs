module Smartian.Fuzz 
#if INTERACTIVE
#r "FSharp.Json.dll"
#endif

open EVMAnalysis
open Utils
open Config
open Options 
open FSharp.Json
open System.IO 
open Newtonsoft.Json; 
open Newtonsoft.Json.Linq
open System
open Smartian.Address
open Nethermind.Core
open System.Text.RegularExpressions

let private makeSingletonSeeds contSpec =
  let constrSpec = contSpec.Constructor
  let funcSpecs = contSpec.NormalFunctions |> Array.toList
  List.map (fun funcSpec -> Seed.init constrSpec [| funcSpec |]) funcSpecs

let private sequenceToSeed contSpec seq =
  let constrSpec = contSpec.Constructor
  let funcSpecs = contSpec.NormalFunctions
  let findSpec s = Array.find (fun spec -> FuncSpec.getName spec = s) funcSpecs
  let funcSpecs = List.map findSpec seq |> List.toArray
  Seed.init constrSpec funcSpecs
  
let private JiaTxt contSpec =
  let constrSpec = contSpec.Constructor
  let funcSpecs = contSpec.NormalFunctions
  Seed.init constrSpec funcSpecs

// 将 FuncSpec 转换为字符串的函数
let funcSpecToString (spec: Seed) : string =
    sprintf "%A" spec

let writeNormalFuncsToFile path (funcSpecs: Seed) =
    printfn "lailelaile"
    // 将 normalFuncs 转换为字符串
    if not (File.Exists(path)) then
        // 如果文件不存在，创建它
      let fileStream = File.Create(path) // 创建文件并打开流
      printfn "create File"
      fileStream.Close() // 关闭文件流
    let arraySpecs = funcSpecs
    let content = funcSpecToString funcSpecs 
    // use writer = new StreamWriter(path, false) // 以追加模式打开文件
    // writer.WriteLine(content) // 写入内容
    File.WriteAllText(path,content)

 
 
let private initializeWithDFA opt =
  let contSpec, seqs = TopLevel.parseAndAnalyze opt.ProgPath opt.ABIPath
  // printfn "init %A" contSpec
  
  let res = JiaTxt contSpec

  let abi = opt.ABIPath
  // let prefix = abi.Remove(abi.Length - 4)
  // printfn "JiaTxt %A" res
  let prefix = "./B3/abi/"
  let suffix = ".bin"
  let startIndex = prefix.Length
  let endIndex = abi.Length - suffix.Length

  let result = abi.Substring(startIndex, endIndex - startIndex)

  // let outputPath = "/home/mingyue/Smartian/B2/normalFuncs/" + result + "_normalFuncs.txt" // 指定输出文件的路径
  // let jsonString = JsonConvert.SerializeObject(res, Formatting.Indented)

  // File.WriteAllText(outputPath,jsonString) // 写入内容

  if List.isEmpty seqs // No DU chain at all.
  then (contSpec, makeSingletonSeeds contSpec)
  else (contSpec, List.map (sequenceToSeed contSpec) seqs)

let private initializeWithoutDFA opt =
  let contSpec = TopLevel.parseOnly opt.ProgPath opt.ABIPath
  (contSpec, makeSingletonSeeds contSpec)

/// Allocate testing resource for each strategy (grey-box concolic testing and
/// random fuzz testing). Resource is managed through 'the number of allowed
/// program execution'. If the number of instrumented program execution exceeds
/// the specified number, the strategy will be switched.
let private allocResource () =
  let concolicEff = GreyConcolic.evaluateEfficiency ()
  let randFuzzEff = RandomFuzz.evaluateEfficiency ()
  let concolicRatio = concolicEff / (concolicEff + randFuzzEff)
  // Bound alloc ratio with 'MinResourceAlloc', to avoid extreme biasing
  let concolicRatio = max MIN_RESOURCE_RATIO (min MAX_RESOURCE_RATIO concolicRatio)
  let randFuzzRatio = 1.0 - concolicRatio
  let totalBudget = EXEC_BUDGET_PER_ROUND
  let greyConcBudget = int (float totalBudget * concolicRatio)
  let randFuzzBudget = int (float totalBudget * randFuzzRatio)
  if greyConcBudget < 0 || randFuzzBudget < 0 then (200, 200)
  else (greyConcBudget, randFuzzBudget)

let private printNewSeeds newSeeds =
  let count = List.length newSeeds
  let concolicStr = String.concat "========\n" (List.map Seed.toString newSeeds)
  log "Generated %d seeds for grey-box concolic : [ %s ]" count concolicStr

let private rewindCursors seed =
  Array.collect Seed.rewindByteCursors (Array.ofList seed)
  |> Array.toList

let rec private greyConcolicLoop opt concQ randQ =
  if Executor.isExhausted () || ConcolicQueue.isEmpty concQ then (concQ, randQ)
  else let seed, concQ = ConcolicQueue.dequeue concQ
       if opt.Verbosity >= 3 then
         log "Grey-box concolic on seed : %s" (Seed.toString seed)
       let newSeeds = GreyConcolic.run seed opt
       // Move cursors of newly generated seeds.
       let rewindedSeeds = rewindCursors newSeeds
       // Also generate seeds by just stepping the cursor of original seed.
       let steppedSeeds = Seed.stepByteCursor seed
       let concQ = List.fold ConcolicQueue.enqueue concQ rewindedSeeds
       let concQ = List.fold ConcolicQueue.enqueue concQ steppedSeeds
       // Note that 'Stepped' seeds are not enqueued for random fuzzing.
       let randQ = List.fold RandFuzzQueue.enqueue randQ newSeeds
       if opt.Verbosity >= 4 then printNewSeeds (rewindedSeeds @ steppedSeeds)
       greyConcolicLoop opt concQ randQ

let private repeatGreyConcolic opt concQ randQ concolicBudget =
  if opt.Verbosity >= 2 then log "Grey-box concoclic testing phase starts"
  Executor.allocateResource concolicBudget
  Executor.resetPhaseExecutions ()
  let tcNumBefore = TCManage.getTestCaseCount ()
  let concQ, randQ = greyConcolicLoop opt concQ randQ
  let tcNumAfter = TCManage.getTestCaseCount ()
  let concolicExecNum = Executor.getPhaseExecutions ()
  let concolicNewTCNum = tcNumAfter - tcNumBefore
  GreyConcolic.updateStatus concolicExecNum concolicNewTCNum
  (concQ, randQ)

let rec private randFuzzLoop opt contSpec concQ randQ =
  // Random fuzzing seeds are involatile, so don't have to check emptiness.
  if Executor.isExhausted () then (concQ, randQ)
  else let seed, randQ = RandFuzzQueue.fetch randQ
       if opt.Verbosity >= 3 then
         log "Random fuzzing on seed : %s" (Seed.toString seed)
       let newSeeds = RandomFuzz.run seed opt contSpec
       let rewindedSeeds = rewindCursors newSeeds
       let concQ = List.fold ConcolicQueue.enqueue concQ rewindedSeeds
       let randQ = List.fold RandFuzzQueue.enqueue randQ newSeeds
       if opt.Verbosity >= 4 then printNewSeeds rewindedSeeds
       randFuzzLoop opt contSpec concQ randQ

let private repeatRandFuzz opt contSpec concQ randQ randFuzzBudget =
  if opt.Verbosity >= 2 then log "Random fuzzing phase starts"
  Executor.allocateResource randFuzzBudget
  Executor.resetPhaseExecutions ()
  let tcNumBefore = TCManage.getTestCaseCount ()
  let concQ, randQ = randFuzzLoop opt contSpec concQ randQ
  let tcNumAfter = TCManage.getTestCaseCount ()
  let randExecNum = Executor.getPhaseExecutions ()
  let randNewTCNum = tcNumAfter - tcNumBefore
  RandomFuzz.updateStatus randExecNum randNewTCNum
  (concQ, randQ)

let rec private fuzzLoop opt contSpec concQ randQ =
  let concolicBudget, randFuzzBudget = allocResource ()
  let concQSize = ConcolicQueue.size concQ
  let randQSize = RandFuzzQueue.size randQ
  if opt.Verbosity >= 2 then
    log "Concolic budget: %d, Rand budget: %d" concolicBudget randFuzzBudget
    log "Concolic queue size: %d, Random Queue size: %d" concQSize randQSize
  // Perform grey-box concolic testing
  let concQ, randQ = repeatGreyConcolic opt concQ randQ concolicBudget
  // Perform random fuzzing
  let concQ, randQ = repeatRandFuzz opt contSpec concQ randQ randFuzzBudget
  fuzzLoop opt contSpec concQ randQ

let private fuzzingTimer opt = async {
  let timespan = System.TimeSpan (0, 0, 0, opt.Timelimit)
  System.Threading.Thread.Sleep (timespan)
  printLine "Fuzzing timeout expired."
  if opt.CheckOptionalBugs then TCManage.checkFreezingEtherBug ()
  log "===== Statistics ====="
  TCManage.printStatistics ()
  log "Done, clean up and exit..."
  exit (0)
}


type SenderConverter() =
    inherit JsonConverter<Sender>()

    override _.WriteJson(writer: JsonWriter, value: Sender, serializer: JsonSerializer) =
        match value with
        | TargetOwner -> writer.WriteValue("TargetOwner")
        | NormalUser1 -> writer.WriteValue("NormalUser1")
        | NormalUser2 -> writer.WriteValue("NormalUser2")
        | NormalUser3 -> writer.WriteValue("NormalUser3")
        | CustomUser name ->
            writer.WriteStartObject()
            writer.WritePropertyName("Case")
            writer.WriteValue("CustomUser")
            writer.WritePropertyName("name")
            writer.WriteValue(name)
            writer.WriteEndObject()

    override _.ReadJson(reader: JsonReader, objectType: Type, existingValue: Sender, hasExistingValue: bool, serializer: JsonSerializer) =
        let json = JObject.Load(reader)
        printfn "ReadJson: %A" json
        match json["Case"].ToString() with
        | "TargetOwner" -> TargetOwner
        | "NormalUser1" -> NormalUser1
        | "NormalUser2" -> NormalUser2
        | "NormalUser3" -> NormalUser3
        | "CustomUser" -> 
            let contrac = json["name"].ToString()
            let addr1 = new Address(contrac)
            if not (List.contains addr1 Address.USER_CONTRACTS) then
              Address.USER_CONTRACTS <- addr1 :: Address.USER_CONTRACTS
              //create an account randomly
              let charArray = contrac.ToCharArray() 
              // change the specific char of the array
              charArray[3] <- '2'
              charArray[6] <- 'a' 
              // transfer the char array to the string
              let account = System.String(charArray) 
              let addr2 = new Address(account) 
              Address.USER_ACCOUNTS <- addr2 :: Address.USER_ACCOUNTS
              Sender.senderList.Add(CustomUser (json["name"].ToString()))
            CustomUser (json["name"].ToString())
        | _ -> failwith "Unknown sender type"

let parseTransactions json =
    // let file = Json.deserialize<Seed[]> json 
    let settings = JsonSerializerSettings()
    settings.Converters.Add(SenderConverter())
    let file = JsonConvert.DeserializeObject<Seed[]>(json, settings)
    file

let loadData path =
    let json = System.IO.File.ReadAllText(path)
    json

let run args =
  let opt = parseFuzzOption args
  assertFileExists opt.ProgPath
  log "Fuzz target : %s" opt.ProgPath
  log "Fuzzing starts at %s" (startTime.ToString("hh:mm:ss"))
  log "Time limit : %d s" opt.Timelimit
  Async.Start (fuzzingTimer opt)
  createDirectoryIfNotExists opt.OutDir
  TCManage.initialize opt.OutDir
  Executor.initialize opt.ProgPath
  let contSpec, initSeeds = if opt.StaticDFA then initializeWithDFA opt
                            else initializeWithoutDFA opt

  // let jsonString = JsonConvert.SerializeObject(initSeeds, Formatting.Indented)
  // // writeNormalFuncsToFile "./seeds.txt" jsonString
  // use writer = new StreamWriter("./seeds.txt", false) // 以追加模式打开文件
  // writer.WriteLine(jsonString) // 写入内容
  
  // // 序列化对象
  // string jsonString = JsonConvert.SerializeObject(initSeeds, Formatting.Indented);

  // // 使用 using 确保自动处理资源
  // using (StreamWriter writer = new StreamWriter("./seeds.txt", false))
  // {
  //     writer.WriteLine(jsonString); // 写入内容
  // }

  // printfn "ABIPath %A" opt.ABIPath
  let input = opt.ABIPath
  let parts = input.Split([| '/' |]) // 先按 '/' 分割
  let fileName = parts.[Array.length parts - 1]
  let name = fileName.Split([| '.' |]).[0] // 再按 '.' 分割并取 AW
  printfn "Extracted name: %s" name // 输出: Extracted name: AW
  let baseDir = "/home/test/tools/GPTSmart/B3/seed" 
  // let baseDir = "./B3/seed"
  let filename = baseDir + "/" + name + "_seed.txt"
      //parseTransactions json
  printfn "filename %s" filename
  // 使用示例
  let transactions = loadData filename  // 读取并解析数据
  let newSeeds = parseTransactions(transactions)
  let initSeeds = List.ofArray newSeeds

 
  let concQ = List.fold ConcolicQueue.enqueue ConcolicQueue.empty initSeeds
  let randQ = List.fold RandFuzzQueue.enqueue (RandFuzzQueue.init ()) initSeeds
  log "Start main fuzzing phase %A" initSeeds.Length
  fuzzLoop opt contSpec concQ randQ
