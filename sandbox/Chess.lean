import Mathlib

inductive Color | white | black
deriving Inhabited, Repr, DecidableEq

def Color.opposite : Color → Color
  | .white => .black
  | .black => .white

inductive UncoloredPiece | pawn | rook | knight | bishop | queen | king
deriving Inhabited, Repr, DecidableEq

structure ColoredPiece where
  color : Color
  piece : UncoloredPiece

inductive File | a | b | c | d | e | f | g | h
deriving Inhabited, Repr, DecidableEq

def File.toNat : File → Nat
  | .a => 1
  | .b => 2
  | .c => 3
  | .d => 4
  | .e => 5
  | .f => 6
  | .g => 7
  | .h => 8

def Nat.toFileD : Nat → File
  | 1 => .a
  | 2 => .b
  | 3 => .c
  | 4 => .d
  | 5 => .e
  | 6 => .f
  | 7 => .g
  | 8 => .h
  | _ => unreachable!

inductive Rank | one | two | three | four | five | six | seven | eight
deriving Inhabited, Repr, DecidableEq

def Rank.toNat : Rank → Nat
  | .one => 1
  | .two => 2
  | .three => 3
  | .four => 4
  | .five => 5
  | .six => 6
  | .seven => 7
  | .eight => 8

def Nat.toRankD : Nat → Rank
  | 1 => .one
  | 2 => .two
  | 3 => .three
  | 4 => .four
  | 5 => .five
  | 6 => .six
  | 7 => .seven
  | 8 => .eight
  | _ => unreachable!

inductive CastlingSide | queenSide | kingSide
deriving Inhabited, Repr, DecidableEq

structure Board where
  data : File → Rank → Option ColoredPiece
  -- turn : Color
  -- enPassantTarget : Option (File × Rank)
  -- hasCastlingRights : Color → CastlingSide → Bool

def initialBoard : Board where
  data
    | .a, .one => .some ⟨.white, .rook⟩
    | .b, .one => .some ⟨.white, .knight⟩
    | .c, .one => .some ⟨.white, .bishop⟩
    | .d, .one => .some ⟨.white, .queen⟩
    | .e, .one => .some ⟨.white, .king⟩
    | .f, .one => .some ⟨.white, .bishop⟩
    | .g, .one => .some ⟨.white, .knight⟩
    | .h, .one => .some ⟨.white, .rook⟩
    | _, .two => .some ⟨.white, .pawn⟩
    | _, .three => .none
    | _, .four => .none
    | _, .five => .none
    | _, .six => .none
    | _, .seven => .some ⟨.black, .pawn⟩
    | .a, .eight => .some ⟨.black, .rook⟩
    | .b, .eight => .some ⟨.black, .knight⟩
    | .c, .eight => .some ⟨.black, .bishop⟩
    | .d, .eight => .some ⟨.black, .queen⟩
    | .e, .eight => .some ⟨.black, .king⟩
    | .f, .eight => .some ⟨.black, .bishop⟩
    | .g, .eight => .some ⟨.black, .knight⟩
    | .h, .eight => .some ⟨.black, .rook⟩
  -- turn := .white
  -- enPassantTarget := none
  -- hasCastlingRights
  --   | _, _ => true

def emptyBoard : Board where
  data
    | _, _ => .none
  -- turn := .white
  -- enPassantTarget := none
  -- hasCastlingRights
  --   | _, _ => true

structure Location where
  file : File
  rank : Rank

structure Move where
  source : Location
  target : Location

def History := List (Board × Move)

#exit

def Board.isLegalMoveIgnoringChecks (board : Board) (move : Move) : Prop :=
  let targetIsEmptyOrEnemy color :=
    (board.data move.target.file move.target.rank).elim True fun target => target.color ≠ color
  let dx := (move.target.file.toNat : ℤ) - (move.source.file.toNat : ℤ)
  let dy := (move.target.rank.toNat : ℤ) - (move.source.rank.toNat : ℤ)
  match board.data move.source.file move.source.rank with
  | .some ⟨color, .rook⟩ =>
    targetIsEmptyOrEnemy color ∧ (dx = 0 ∨ dy = 0) ∧
    ∀ k ∈ Finset.Ioo 0 |dx ⊔ dy|,
      let file := (move.source.file.toNat + k * Int.sign dx).toNat.toFileD
      let rank := (move.source.rank.toNat + k * Int.sign dy).toNat.toRankD
      (board.data file rank).isNone
  | .some ⟨color, .knight⟩ =>
    targetIsEmptyOrEnemy color ∧ ((|dx| = 2 ∧ |dy| = 1) ∨ (|dx| = 1 ∧ |dy| = 2))
  | .some ⟨color, .bishop⟩ =>
    targetIsEmptyOrEnemy color ∧ |dx| = |dy| ∧
    ∀ k ∈ Finset.Ioo 0 |dx ⊔ dy|,
      let file := (move.source.file.toNat + k * Int.sign dx).toNat.toFileD
      let rank := (move.source.rank.toNat + k * Int.sign dy).toNat.toRankD
      (board.data file rank).isNone
  | .some ⟨color, .queen⟩ =>
    targetIsEmptyOrEnemy color ∧ (dx = 0 ∨ dy = 0 ∨ |dx| = |dy|) ∧
    ∀ k ∈ Finset.Ioo 0 |dx ⊔ dy|,
      let file := (move.source.file.toNat + k * Int.sign dx).toNat.toFileD
      let rank := (move.source.rank.toNat + k * Int.sign dy).toNat.toRankD
      (board.data file rank).isNone
  | .some ⟨color, .king⟩ =>
    (targetIsEmptyOrEnemy color ∧ (|dx| ≤ 1 ∧ |dy| ≤ 1) ∧ (dx ≠ 0 ∨ dy ≠ 0)) ∨
    (dx = 2 ∧ dy = 0 ∧ board.hasCastlingRights color .kingSide) ∨
    (dx = -2 ∧ dy = 0 ∧ board.hasCastlingRights color .queenSide)
  | .some ⟨color, .pawn⟩ =>
    let fwd := if color = .white then 1 else -1
    dx = 0 ∧ (
      (dy = fwd ∧ (board.data move.target.file move.target.rank).isNone) ∨
      (dy = 2 * fwd ∧ (board.data move.target.file move.target.rank).isNone ∧
        move.source.rank = if color = .white then .two else .seven)) ∨
    |dx| = 1 ∧ dy = fwd ∧ (
      match board.data move.target.file move.target.rank with
      | .some target => target.color ≠ color
      | .none => board.enPassantTarget.elim False fun (epFile, epRank) =>
        (board.data epFile epRank).elim False (fun ep => ep.color ≠ color) ∧
        move.target.file = epFile ∧ move.source.rank = epRank)
  | .none => False


-- implementation is wrong, a knight can break castling rights by capturing a rook for example
def Board.applyMove (board : Board) (move : Move) : Board :=
  let dx := (move.target.file.toNat : ℤ) - (move.source.file.toNat : ℤ)
  let dy := (move.target.rank.toNat : ℤ) - (move.source.rank.toNat : ℤ)
  match board.data move.source.file move.source.rank with
  | .some ⟨color, .rook⟩ => {
      data := fun file rank =>
        if file = move.source.file ∧ rank = move.source.rank then none
        else if file = move.target.file ∧ rank = move.target.rank then .some ⟨color, .rook⟩
        else board.data file rank
      turn := color.opposite
      enPassantTarget := none
      hasCastlingRights := fun castlingColor side =>
        match color, castlingColor, side, move.source.file, move.source.rank with
        | .white, .white, .queenSide, .a, .one => false
        | .white, .white, .kingSide, .h, .one => false
        | .black, .black, .queenSide, .a, .eight => false
        | .black, .black, .kingSide, .h, .eight => false
        | _, _, _, _, _ => board.hasCastlingRights castlingColor side
    }
  | .some ⟨color, .knight⟩ => {
      data := fun file rank =>
        if file = move.source.file ∧ rank = move.source.rank then none
        else if file = move.target.file ∧ rank = move.target.rank then .some ⟨color, .knight⟩
        else board.data file rank
      turn := color.opposite
      enPassantTarget := none
      hasCastlingRights := board.hasCastlingRights
    }
  | .some ⟨color, .bishop⟩ => {
      data := fun file rank =>
        if file = move.source.file ∧ rank = move.source.rank then none
        else if file = move.target.file ∧ rank = move.target.rank then .some ⟨color, .bishop⟩
        else board.data file rank
      turn := color.opposite
      enPassantTarget := none
      hasCastlingRights := board.hasCastlingRights
    }
  | .some ⟨color, .queen⟩ => {
      data := fun file rank =>
        if file = move.source.file ∧ rank = move.source.rank then none
        else if file = move.target.file ∧ rank = move.target.rank then .some ⟨color, .queen⟩
        else board.data file rank
      turn := color.opposite
      enPassantTarget := none
      hasCastlingRights := board.hasCastlingRights
    }
  | .some ⟨color, .king⟩ =>
    if dx = 2 then
      sorry
    else if dx = -2 then
      sorry
    else {
      data := fun file rank =>
        if file = move.source.file ∧ rank = move.source.rank then none
        else if file = move.target.file ∧ rank = move.target.rank then .some ⟨color, .king⟩
        else board.data file rank
      turn := color.opposite
      enPassantTarget := none
      hasCastlingRights := fun castlingColor side =>
        if color = castlingColor then false
        else board.hasCastlingRights castlingColor side
    }
  | .some ⟨color, .pawn⟩ =>
    sorry
  | .none => board



def ColoredPiece.toString : ColoredPiece → String
  | ⟨.black, .pawn⟩ => "♟"
  | ⟨.white, .pawn⟩ => "♙"
  | ⟨.black, .rook⟩ => "♜"
  | ⟨.white, .rook⟩ => "♖"
  | ⟨.black, .knight⟩ => "♞"
  | ⟨.white, .knight⟩ => "♘"
  | ⟨.black, .bishop⟩ => "♝"
  | ⟨.white, .bishop⟩ => "♗"
  | ⟨.black, .queen⟩ => "♛"
  | ⟨.white, .queen⟩ => "♕"
  | ⟨.black, .king⟩ => "♚"
  | ⟨.white, .king⟩ => "♔"

def Board.toString (board : Board) : String :=
  let ranks : List Rank := [.one, .two, .three, .four, .five, .six, .seven, .eight].reverse
  let files : List File := [.a, .b, .c, .d, .e, .f, .g, .h]
  String.join <| ranks.map fun rank =>
    (String.append · "\n") <| String.join <| files.map fun file =>
      match board.data file rank with
      | .none => if (rank.toNat + file.toNat) % 2 == 1 then "▮" else "▯"
      | .some piece => piece.toString

-- #eval IO.println initialBoard.toString

def main : IO Unit := do
      let stdin ← IO.getStdin
      IO.println "Please enter your name:"
      let name ← stdin.getLine
      IO.println s!"Hello, {name}!"

-- #eval main

-- 4:17

-- example {α} (o : Option α) (p : α → Prop) : Prop :=
--     o.elim True p
