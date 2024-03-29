sig Task {}

var sig Pending in Task {}
var sig Done in Task {}

// Finish the specification of the behavior of the todo 
// concept, trying to ensure the operational principles in 
// http://alloy4fun.inesctec.pt/dWD66Kod79MSMRiPh

pred add [t : Task] {
	// Adding a task to the pending
  t not in Pending+Done
  
  Pending' = Pending+t
  Done' = Done

}

pred complete [t : Task] {
	// Complete a pending task
t in Pending
  t in Done'
  
  Pending' = Pending - t
  Done' = Done+t
//'
}

pred delete [t : Task] {
	// Delete a task
  t in Pending+Done
  
  Pending' = Pending - t
  Done' = Done-t
}

pred stutter {
	// Stuttering
  Pending' = Pending
  Done'=Done

}

pred behavior {
	// Initial state
  	no Done
  	no Pending
	always (no Done & Pending) 

	// Transitions
	always (stutter or some t : Task | add[t] or complete[t] or delete[t])
}

