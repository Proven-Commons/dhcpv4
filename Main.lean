/-
  Command line front end, used by the tests.

  Reads one request per line and prints one answer per line. A
  request is an operation and its input as comma-separated
  decimal byte codes.

    parse 1,1,6,0,...   prints  ok:1,1,6,0,... or none

  The one operation is `parse`. Its input is the byte codes of
  a DHCPv4 message. Its answer is `ok:` and the byte codes of
  the canonical reprint of the parsed message, or `none` when
  the message is rejected. The canonical reprint writes the
  fixed fields as they stood, the options with no pad bytes,
  and exactly one end byte; see SPEC.md.

  A request is an operation, then optionally one space and its
  numbers; with no numbers after the space, the input is empty.
  A malformed request prints `error`: any other line, an unknown
  operation, a number that is not plain decimal digits, or a
  code above 255, which no byte holds. A line may end in LF or
  CR LF; nothing else around a request is ignored.

  The parsing and printing here call `Dhcp.parse` and
  `Dhcp.print` directly. The line handling is covered by the
  tests, not by a proof.
-/

import Dhcp

open Dhcp

/-- A number in plain decimal digits. Longer numbers than any
    byte code are refused before they are converted, since
    that takes time quadratic in their length. -/
def number (t : String) : Option Nat :=
  let ds := t.toList
  if ds.isEmpty || !ds.all Char.isDigit || (ds.dropWhile (· = '0')).length > 7 then none
  else t.toNat?

/-- The comma-separated numbers in `s`. -/
def numbers (s : String) : Option (List Nat) :=
  if s.isEmpty then some [] else (s.splitOn ",").mapM number

/-- The numbers as bytes. A number above 255 is not a byte, and
    makes the request malformed. -/
def toBytes (ns : List Nat) : Option (List UInt8) :=
  ns.mapM fun n => if n < 256 then some n.toUInt8 else none

def showCodes (bs : List UInt8) : String :=
  ",".intercalate (bs.map fun b => toString b.toNat)

/-- The answer to one request, or `none` when the request is
    malformed. -/
def answer (op : String) (ns : List Nat) : Option String :=
  match op with
  | "parse" =>
    match toBytes ns with
    | none => none
    | some bs =>
      match parse bs with
      | some v => some ("ok:" ++ showCodes (print v))
      | none => some "none"
  | _ => none

/-- The answer to one line: an operation, then optionally one
    space and its numbers. -/
def request (line : String) : Option String :=
  match line.splitOn " " with
  | [op] => answer op []
  | [op, arg] => numbers arg >>= answer op
  | _ => none

/-- The line without its line ending: LF, or CR LF. -/
def chomp (line : String) : String :=
  let cs := line.toList
  if cs.getLast? = some '\n' then
    let cs := cs.dropLast
    String.ofList (if cs.getLast? = some '\r' then cs.dropLast else cs)
  else line

def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let line := chomp line
    stdout.putStrLn ((request line).getD "error")
