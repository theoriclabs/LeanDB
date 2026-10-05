/- The declaration commands, one per line in any order: an identifier-led command never
   swallows the next line (`internal Game.insert` followed by `link …`), and a represented
   private-constructor type with a lambda encoder is an entity field. -/
import LeanDb.Model
open LeanDb.Model

namespace CommandsFixture

structure Move where
  row : Nat
  col : Nat
  deriving Domain, BEq

structure Board where
  private mk ::
  moves : List Move

def Board.replay (moves : List Move) : Except String Board :=
  if moves.length ≤ 9 then .ok ⟨moves⟩ else .error "too many moves"

/-- A board is stored as its moves. -/
represent Board as List Move by (·.moves) checked Board.replay

structure Player where
  name : Name
  email : Email
  deriving Entity

structure Game where
  board : Board
  owner : Ref Player
  deriving Entity

structure Seat where
  game : Ref Game
  player : Ref Player
  deriving Entity

constraint Player.uniqueEmail : unique email
constraint Seat.onePerGame : unique (game, player)
constraint Seat.removeWithGame : cascade game
internal Game.insert
link Seat.game Seat.player
internal Seat.select
deriving instance Changes (except := [owner]) for Game

/-- info: CommandsFixture.Game.patch : Row Game → Game.Changes → DB Unit -/
#guard_msgs in #check Game.patch
/-- info: CommandsFixture.Seat.link.game.player : LinkKey Seat Game Player -/
#guard_msgs in #check Seat.link.game.player
/-- info: CommandsFixture.Seat.findBy : Ref Game → Ref Player → Query (Option (Row Seat)) -/
#guard_msgs in #check Seat.findBy
#guard (Domain.fields (T := Game)).map (fun f => (f.name, f.kind == .value)) == [("board", true), ("owner", false)]

end CommandsFixture
