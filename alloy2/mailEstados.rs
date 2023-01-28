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

// Finish the specification of the behavior of the email 
// concept, trying to ensure the operational principles in 
// http://alloy4fun.inesctec.pt/RnQaRZEFQhKmnLYcL

pred send[f, t : User, c : Content] {
	// A message is sent from user f to t with content c
  some m:Message {
    
    	m.from=t
    	m.to=f
    	m.content=c
    
	Undelivered' = Undelivered +  m
    historically m not in Undelivered
    //historically m not in User.inbox
    all u : User | u.inbox' = u.inbox 
    }
}

pred receive[t : User, m : Message] {
	// A sent message m is received by user t
	m in Undelivered
  	Undelivered' = Undelivered - m
  	m.to = t
  	m in t.inbox'
    //'
  	t.inbox' = t.inbox + m 
    //'
    all u : User-t | u.inbox' = u.inbox
    //'
}

pred stutter {
	// Stuttering
	Undelivered' =Undelivered
  	all u : User | u.inbox' = u.inbox 
	//'
}

pred behavior {
	// Initial state
	no Undelivered
 	all u : User | no u.inbox

	// Actions
	always {
		stutter or 
		(some t,f : User, c : Content | send[f,t,c]) or
		(some t : User, m : Message | receive[t,m])
	}
}
