/- A row is tied to the transaction scope it was read in. -/
import TestsModel.Post
open LeanDb.Model
def wrong {Scope : Type} (row : Row Scope Party) : Row Unit Party := row
