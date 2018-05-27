Require Ascii.
Require Import String.

Require Import SimpleIO.IOMonad.
Require Import SimpleIO.CoqPervasives.

Import IONotations.
Open Scope io_scope.

Parameter supports_ansi : out_channel -> IO bool.

Parameter clear_line : out_channel -> IO unit.

(* Ported from Haskell's ansi-terminal library.
   Heuristics to determine whether a channel supports ANSI codes:
   - Is a terminal
   - TERM is not "dumb" *)
Extract Constant supports_ansi =>
  "CoqSimpleIO.Impure.mk_io_1 (fun h ->
     Unix.isatty (Unix.descr_of_out_channel h) &&
     Sys.getenv ""TERM"" <> ""dumb"")".

Extract Constant clear_line =>
  "CoqSimpleIO.Impure.mk_io_1 (fun h ->
     output_string h ""\r\027[K"")".

Inductive Terminal :=
  MkTerminal
    (output : string -> IO unit)
    (clear_output : string -> IO unit)
    (update : string -> IO unit).

Definition output_term : Terminal -> string -> IO unit :=
  fun '(MkTerminal out _ _) => out.

Definition clear_output_term : Terminal -> string -> IO unit :=
  fun '(MkTerminal _ cout _) => cout.

Definition update_term : Terminal -> string -> IO unit :=
  fun '(MkTerminal _ _ upd) => upd.

Definition noTerminal : Terminal :=
  MkTerminal
    (fun _ => ret tt)
    (fun _ => ret tt)
    (fun _ => ret tt).

Definition withNoTerminal {a} : (Terminal -> IO a) -> IO a :=
  fun k => k noTerminal.

Definition withStdTerminal {a} : (Terminal -> IO a) -> IO a :=
  fun k =>
    b <- supports_ansi stdout;;
    let std_output s := print_string s;; print_newline in
    k (if b then
         let clear_out s := clear_line stdout;; print_string s in
         let std_clear_output s := clear_out s;; print_newline in
         let std_update s := clear_out s;; flush stdout in
         MkTerminal std_output std_clear_output std_update
       else
         let no_update _ := ret tt in
         MkTerminal std_output std_output no_update).
