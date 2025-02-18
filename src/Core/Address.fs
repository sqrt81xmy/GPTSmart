module Smartian.Address

open Utils
open BytesUtils
open Nethermind.Core

/// Converts an address into a string.
let toStr (addr: Address) = addr.ToString()

let toBytes endian (addr: Address) =
  toStr addr |> hexStrToBytes
  |> if endian = LE then Array.rev else identity

/// Converts a byte array into an Address.
let fromBytes endian (bytes: byte[]) =
  if endian = LE then new Address(Array.rev bytes) else new Address(bytes)

/// Converts a hex string into an Address.
let fromStr (s: string) = new Address(s)

let ZERO = fromStr("0000000000000000000000000000000000000000")
let MINER = fromStr("76e68a8696537e4141926f3e528733af9e237d69")
let OWNER_ACCOUNT = fromStr("b7705ae4c6f81b66cdb323c65f4e8133690fc099")
let OWNER_CONTRACT = fromStr("24cd2edba056b7c654a50e8201b619d4f624fdda")
let TARG_CONTRACT = fromStr("6b773032d99fb9aad6fc267651c446fa7f9301af")
let private USER_ACCNT_1 = fromStr("00120000000000000000000000000000000001d2")
let private USER_CONTR_1 = fromStr("118a2c24808934116e6ab4c00ff48145d23b09e1")
let private USER_ACCNT_2 = fromStr("001200000000000000000000000000000000021c")
let private USER_CONTR_2 = fromStr("226cc61b3eac93cc2cc9d6cb8d61856670d50fad")
let private USER_ACCNT_3 = fromStr("0012000000000000000000000000000000000229")
let private USER_CONTR_3 = fromStr("33b808a5ae24c410e8739b5ca2d5ef3931d3e09f")
let USER_ACCNT_4 = fromStr("0012000000000000000000000000000000000231")
let USER_CONTR_4 = fromStr("0xf925a82b8c26520170c8d51b65a7def6364877b3")
let USER_ACCNT_5 = fromStr("0012000000000000000000000000000000000259")
let USER_CONTR_5 = fromStr("0x1d3b2638a7cc9f2cb3d298a3da7a90b67e5506ed")
let USER_ACCNT_6 = fromStr("0012000000000000000000000000000000000263")
let USER_CONTR_6 = fromStr("0x51efaf4c8b3c9afbd5ab9f4bbc82784ab6ef8fcc")
let mutable USER_ACCOUNTS = [USER_ACCNT_1; USER_ACCNT_2; USER_ACCNT_3; USER_ACCNT_4; USER_ACCNT_5; USER_ACCNT_6]
let mutable USER_CONTRACTS = [USER_CONTR_1; USER_CONTR_2; USER_CONTR_3; USER_CONTR_4; USER_CONTR_5; USER_CONTR_6]

// The adress that we use to send transactions, is the agent contract's deployer.
let accountOf = function
  | TargetOwner -> OWNER_ACCOUNT
  | NormalUser1 -> USER_CONTR_1
  | NormalUser2 -> USER_CONTR_2
  | NormalUser3 -> USER_CONTR_3
  | NormalUser4 -> USER_CONTR_4
  | NormalUser5 -> USER_CONTR_5
  | NormalUser6 -> USER_CONTR_6
  | CustomUser name -> fromStr(name) 

let contractOf = function
  | TargetOwner -> OWNER_CONTRACT
  | NormalUser1 -> USER_CONTR_1
  | NormalUser2 -> USER_CONTR_2
  | NormalUser3 -> USER_CONTR_3
  | NormalUser4 -> USER_CONTR_4
  | NormalUser5 -> USER_CONTR_5
  | NormalUser6 -> USER_CONTR_6
  | CustomUser name -> fromStr(name) // 处理自定义用户

// Return an address that can be used as an Address type input.
let pickInteresting () =
  pickFromList (ZERO :: OWNER_CONTRACT :: TARG_CONTRACT :: USER_CONTRACTS)
