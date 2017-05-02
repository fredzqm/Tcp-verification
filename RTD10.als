module RTD10
open util/ordering[Time]
open packet

// modeling sender state
abstract sig SState {}
one sig WaitForCallFromAbove extends SState {}
one sig WaitForACKorNAK extends SState {}

// modeling reciever state
abstract sig RState {}
one sig WaitForCallFromBelow extends RState {}

// modeling time or state of the system
sig Time {
	sbuffer: set RealData,
	sstate: SState,
	lastData: lone RealData,
	rbuffer: set RealData,
	rstate: RState,
	to: lone Packet,
	back: lone Packet
}

// beginning of the system
pred Time.init[]{
	this.sbuffer = RealData
	this.sstate = WaitForCallFromAbove
	this.rbuffer = none
	this.rstate = WaitForCallFromBelow
	this.to = none
	this.back = none
}
run init for 3 but 1 Time, 3 Data

// end of the state
pred Time.end[]{
	this.sbuffer = none
	this.sstate = WaitForCallFromAbove	
	this.rbuffer = RealData
	this.rstate = WaitForCallFromBelow
	this.to = none
	this.back = none
}
run end for 3 but 1 Time, 3 Data

// data sent to the link
pred sendData[t, t': Time] {
	t.sstate = WaitForCallFromAbove
	t'.sstate = WaitForACKorNAK
	t.rstate = t'.rstate
	t.to = none
	t.back = none
	t'.back = none
	one d : t.sbuffer | {
		make_pkt[d, t'.to]
		t.sbuffer - d = t'.sbuffer
		t'.lastData = d
	}
	t.rbuffer = t'.rbuffer
}
run sendData

// date recieved from the link
pred recieveData[t, t': Time] {
	t.sstate = t'.sstate
	t.rstate = t'.rstate
	t.to != none
	t'.to = none
	t.back = none
	let p = t.to | {
		p.NOTcorrupt[] => (
			t.rbuffer + p.data = t'.rbuffer and
			make_pkt[ACK, t'.back]
		) else (
			make_pkt[NAK, t'.back]
		)
	}
	t.sbuffer = t'.sbuffer
}
run recieveData

// date recieved from the link
pred recieveACK[t, t': Time] {
	t.sstate = WaitForACKorNAK
	t.to = none
	t.back != none
	t'.back = none
	let p = t.back | {
		// did not check corruption here
		(p.isNAK[] => (
			t'.sstate = WaitForACKorNAK and
			make_pkt[	t.lastData, t'.to] and
			t'.lastData = t.lastData
		)) and
		(p.isACK[] => (
			t'.to = none and
			t'.sstate = WaitForCallFromAbove
		))
	}
	t.sbuffer = t'.sbuffer
	t.rbuffer = t'.rbuffer
}
run recieveACK

// model the corruption of data in the link
pred corruptData[t, t': Time] {
	t.sstate = t'.sstate
	t.rstate = t'.rstate
	t.lastData = t'.lastData
	t.sbuffer = t'.sbuffer
	t.rbuffer = t'.rbuffer
	corrupt[t.to, t'.to]
	t.back = t'.back
}

// all valid transition with something happening
pred transition[t, t': Time] {
	sendData[t, t'] or
	corruptData[t, t'] or
	recieveACK[t, t'] or
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
run possibleReliabe for 7 but exactly 1 RealData

assert alwaysReliable {
	traces =>	last[].end[]
}

check alwaysReliable  for 5 but exactly 8 Time, 1 RealData



//M1:Comment
// produce a counter example, because there is not enough time elapsed

// produces no counter example, because all packets eventually arrive
//check alwaysReliable  for 5 but exactly 11 Time, 5 RealData

