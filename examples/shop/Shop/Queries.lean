import Shop.Entities

/-! # Queries

Domain logic as plain defs over `select`. Predicates and sort keys are
ordinary Lean — the compiler checks them against the row types.
-/

namespace Shop

open LeanDb

/-- Purchases the shop still owes work on (placed/paid/shipped), oldest
    first. `OrderStatus.isActive` is a `match` on a closed enum, so the
    planner narrows it into SQL as case splits on the stored variant —
    the lambda still runs on decoded rows. -/
def activeOrders : DbM (Array (Stored Purchase)) :=
  select [Purchase] (fun o => o.val.status.isActive) (.key (·.val.placedAt))

/-- Products with stock strictly below `threshold`, emptiest shelf first. -/
def lowStock (threshold : Nat) : DbM (Array (Stored Product)) :=
  select [Product] (fun p => p.val.stock < threshold)
    (.andThen (.key (·.val.stock)) (.key (·.val.name)))

/-- The contents of one purchase: its line items joined with their
    products, alphabetical by product name. -/
def basketOf (o : Ref Purchase) : DbM (Array (Stored LineItem × Stored Product)) :=
  select [LineItem, Product]
    (fun (li, p) => li.val.order == o && li.val.product == p.ref)
    (.key fun (_, p) => p.val.name)

/-- Delivered purchases joined with their line items — the rows revenue is
    computed from. Oldest purchase first, line items in insertion order. -/
def revenueRows : DbM (Array (Stored Purchase × Stored LineItem)) :=
  select [Purchase, LineItem]
    (fun (o, li) => li.val.order == o.ref && o.val.status == OrderStatus.delivered)
    (.andThen (.key fun (o, _) => o.val.placedAt) (.key fun (_, li) => li.id.toInt64))

/-- What one line item contributes, in cents. -/
def LineItem.totalCents (li : LineItem) : Nat :=
  li.qty.count.toNat * li.unitPrice.cents

/-- Total revenue over `revenueRows` output, in cents. -/
def revenueCents (rows : Array (Stored Purchase × Stored LineItem)) : Nat :=
  rows.foldl (fun acc (_, li) => acc + li.val.totalCents) 0

end Shop
