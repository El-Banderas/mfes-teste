sig User {
	var inbox : set Message
}
sig Content {}
sig Message {
	from : User,
	to : User,
	content : Content
}
var sig Undelivered in Message {}

// Specify the following operational principles.

// Assume the existence of the following actions:
// pred send[f : User, t : User, c : Content] {...}
// pred receive[t : User, m : Message] {...}
// pred stutter {...}

// Counter-examples may depict systems that are purposely badly implemented.


pred op6 {
	// After a receive the respective message is no longer undelivered
	all m : Message | all u : User |
  		always (receive[u, m] implies after m not in Undelivered) 
}


pred op7 {
	// A message that becomes undelivered has never been undelivered before
	all m : Message |
  		always (m not in Undelivered and m in Undelivered' implies historically m not in Undelivered )
  	//'
}


pred op8 { // Ver este
	// If all possible messages have been received nothing else can happen
	always (Message = User.inbox => always stutter)
}


pred op9 {
	// Any received message was undelivered since it was sent
	all m : Message | all u : User |
  		always (receive[u,m] implies m in Undelivered since send[m.from, m.to, m.content])	
  
}


pred op10 {
	// After a send the respective message can only stop being undelivered after being received
	all m : Message | all u : User |
  	always (send[m.from, m.to, m.content] implies (after m in Undelivered until receive[u,m]))	

}



pred op1 {
	// All messages in the inbox of an user are addressed to that user
	all u : User | all m : Message | always (m in u.inbox implies m.to = u) 
	// Porque é que aqui não podia ser:
  	//all u : User | all m : u.inbox | always (m.to = u)
}


pred op2 {
	// Undelivered messages cannot be in any inbox
	all m : Message | all u : User | always(m in Undelivered implies m not in u.inbox) 
}
pred op3 {
	// Any received message must have been sent before

	all x: Message | all u : User | 
  		always (receive[u,x] implies once send[x.from,x.to,x.content])
}    


pred op4 {
	// A message in an inbox can never be undelivered again
	all m : Message | all u : User | 
  		always (m in u.inbox implies always m not in Undelivered )
}


pred op5 { // ?
	// If no messages are ever sent there will never be undelivered messages
//	all m : Message | all u : User | 
//  		always ( send[m.from, m.to, m.content] implies no Undelivered)
	
  // always ( implies historically )
}
