module sender
open packet

abstract sig SState {}
one sig WaitForCallFromAbove extends SState {}

sig Sender {
	buffer: Data,
	sstate: SState
}

pred Sender.init[] {
	this.buffer = Data
	this.sstate = WaitForCallFromAbove
}

pred Sender.end[] {
	this.buffer = none
	this.sstate = WaitForCallFromAbove
}
