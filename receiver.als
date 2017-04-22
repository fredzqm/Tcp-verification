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
