namespace Smartian

open Nethermind.Core
open Utils 
open BytesUtils

type Hash = uint64

type Signedness = Signed | Unsigned

type Sign = Positive  | Negative | Zero

/// Direction that the cursor of a 'Seed' should move toward.
type Direction = Stay | Left | Right

/// The type of agent contract. Note that Smartian, Contractfuzzer, sFuzz have
/// slightly different agent contract code. We support only sFuzz for now.
type AgentType =
  | NoAgent
  | SmartianAgent of Address
  | SFuzzAgent of Address
 
type Sender =
  | TargetOwner
  | NormalUser1
  | NormalUser2
  | NormalUser3
  | NormalUser4
  | NormalUser5
  | CustomUser of string

module Sender =
  let mutable senderList = ResizeArray<Sender>([TargetOwner; NormalUser1; NormalUser2; NormalUser3])
  let pick () =
    // transfer ResizeArray<Sender> to `Sender list`
    let senderFSharpList = List.ofSeq senderList 
    // call pickFromList function
    pickFromList senderFSharpList
    // pickFromList List.ofSeq[TargetOwner; NormalUser1; NormalUser2; NormalUser3]