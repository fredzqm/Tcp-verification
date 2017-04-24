module RTD10
open util/ordering[Time]
open packet

// modeling sender state
abstract sig SState {}
one sig WaitForCallFromAbove extends SState {}

// modeling reciever state
abstract sig RState {}
one sig WaitForCallFromBelow extends RState {}

// modeling time or state of the system
sig Time {
	sbuffer: set Data,
	sstate: SState,
	rbuffer: set Data,
	rstate: RState,
	packets: set Packet
}

// beginning of the system
pred Time.init[]{
	this.sbuffer = Data
	this.sstate = WaitForCallFromAbove
	this.rbuffer = none
	this.rstate = WaitForCallFromBelow
	this.packets = none
}
run init for 3 but 1 Time, 3 Data

// end of the state
pred Time.end[]{
	this.sbuffer = none
	this.sstate = WaitForCallFromAbove	
	this.rbuffer = Data
	this.rstate = WaitForCallFromBelow
	this.packets = none
}
run end for 3 but 1 Time, 3 Data

// data sent to the link
pred sendData[t, t': Time] {
	t.sstate = t'.sstate
	t.rstate = t'.rstate
	one d : t.sbuffer | one p : Packet | (
		make_pkt[d, p] and
		t.sbuffer - d = t'.sbuffer and
		p not in t.packets and
		t.packets + p = t'.packets
	)
	t.rbuffer = t'.rbuffer
}

// date recieved from the link
pred recieveData[t, t': Time] {
	t.sstate = t'.sstate
	t.rstate = t'.rstate
	one p : t.packets | one d : Data | (
		extract[p, d] and
		d not in t.rbuffer and
		t.rbuffer + d = t'.rbuffer and
		t.packets - p = t'.packets
	)
	t.sbuffer = t'.sbuffer
}

// all valid transition with something happening
pred transition[t, t': Time] {
	sendData[t, t'] or
	recieveData[t, t']
}

// traces of the system
pred traces {
	first[].init[]
	all t : Time - last[] | transition[t, t.next[]]
}

pred possibleReliabe {
	traces
	some t : Time | t.end[]
}
run possibleReliabe for 7 but 3 Data

assert alwaysReliable {
	traces =>	last[].end[]
}
// produce a counter example, because there is not enough time elapsed
check alwaysReliable  for 5 but exactly 10 Time, 5 Data
// produces no counter example, because all packets eventually arrive
check alwaysReliable  for 5 but exactly 11 Time, 5 Data

