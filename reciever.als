module reciever
open packet

abstract sig RState {}
one sig WaitForCallFromBelow extends RState {}

sig Reciever {
	buffer: set Data,
	rstate: RState
}

pred Reciever.init[] {
	this.buffer = none
	this.rstate = WaitForCallFromBelow
}

pred Reciever.end[] {
	this.buffer = Data
	this.rstate = WaitForCallFromBelow
}

run init
