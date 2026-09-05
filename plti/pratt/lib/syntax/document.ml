open Core

(* Keep every human-facing rendering at the same width, including diagnostics
   and tests. Printers return documents so callers can embed them without first
   committing to a line layout. *)
let string_of_document doc =
  let buffer = Buffer.create 128 in
  PPrint.ToBuffer.pretty 0.8 80 buffer doc;
  Buffer.contents buffer

let output channel doc = PPrint.ToChannel.pretty 0.8 80 channel doc

let quoted text = PPrint.dquotes (PPrint.string (String.escaped text))
