module sender
open link

abstract sig SState {}
one sig WaitForCallFromAbove extends SState {}

sig Sender {
	buffer: set Data,
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

run init

pred rdt_send[s, s': Sender, l, l' : Link] {
	s.sstate = s'.sstate
	one d : s.buffer | one p : Packet | (
		make_pkt[d, p] and
		s.buffer - d = s'.buffer and
		l.packets + p = l'.packets
	)
}
