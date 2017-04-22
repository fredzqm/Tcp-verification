module receiver
open link

abstract sig RState {}
one sig WaitForCallFromBelow extends RState {}

sig Receiver {
	buffer: set Data,
	rstate: RState
}

pred Receiver.init[] {
	this.buffer = none
	this.rstate = WaitForCallFromBelow
}

pred Receiver.end[] {
	this.buffer = Data
	this.rstate = WaitForCallFromBelow
}

run init

pred rdt_rcv[r, r': Receiver, l, l' : Link] {
	r.rstate = r'.rstate
	one p : l.packets | one d : Data | (
		extract[p, d] and
		r.buffer + d = r'.buffer and
		l.packets - p = l'.packets
	)
}
