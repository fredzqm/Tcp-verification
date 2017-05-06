module RTD10
open util/ordering[Time]

// model sequence number
abstract sig Seq {}
one sig One extends Seq {}
one sig Zero extends Seq	 {}

fun Seq.nextSeg[] : Seq {
	this = One => Zero else One
}

// modeling sender state
abstract sig SState {}
abstract sig WaitForCallFromAbove extends SState {
	seg1: Seq
}
one sig WaitForCallFromAbove1 extends WaitForCallFromAbove {}{seg1 = One}
one sig WaitForCallFromAbove0 extends WaitForCallFromAbove {}{seg1 = Zero}

abstract sig WaitForACKorNAK extends SState {
	seg2: Seq
}
one sig WaitForACKorNAK1 extends WaitForACKorNAK {}{seg2 = One}
one sig WaitForACKorNAK0 extends WaitForACKorNAK {}{seg2 = Zero}

// modeling reciever state
abstract sig RState {}
abstract sig WaitForFromBelow extends RState {
	seg3: Seq
}
one sig WaitForFromBelow1 extends WaitForFromBelow {}{seg3 = One}
one sig WaitForFromBelow0 extends WaitForFromBelow {}{seg3 = Zero}

// ensuring that two distinct State must has different sequence number
fact stateConstrait {
(	all disjoint a, b : WaitForACKorNAK | a.seg2 != b.seg2) and 
	#WaitForACKorNAK = 2 and 
(	all disjoint a, b : WaitForCallFromAbove | a.seg1 != b.seg1) and
	#WaitForCallFromAbove = 2 and 
(	all disjoint a, b : WaitForFromBelow | a.seg3 != b.seg3) and 
	#WaitForFromBelow = 2
}
run {}

sig CheckSum {}
abstract sig Data {
	checksum: CheckSum
}
fact{
	all disj d,d':Data|
		d.checksum!=d'.checksum		
}

sig RealData extends Data {}
one sig ACK extends Data {}
one sig NAK extends Data {}

sig Packet {
	data: Data,
	seg: Seq,
	checksum: CheckSum
}

pred make_pkt[segT : Seq, d : Data, p : Packet] {
	p.data = d
	p.seg = segT
	p.checksum = d.checksum
}

pred extract[p : Packet, d : Data] {
	p.data = d
	p.checksum = d.checksum
}

pred Packet.isNAK[]{
	this.data = NAK
}

pred Packet.isACK[]{
	this.data = ACK
}

pred corrupt[p, p' : Packet] {
	p != none
	p != p'
	p' != none
}

pred Packet.NOTcorrupt[]{
	this.checksum = this.data.checksum
}

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
	this.sstate.seg1=Zero
	this.rbuffer = none
	this.rstate.seg3 =Zero
	this.to = none
	this.back = none
}
run init for 3 but 1 Time, 3 Data

// end of the state
pred Time.end[]{
	this.sbuffer = none
	this.sstate in WaitForCallFromAbove	
	this.rbuffer = RealData
	this.rstate in WaitForFromBelow
	this.sstate.seg1 = this.rstate.seg3
	this.to = none
	this.back = none
}
run end for 3 but 1 Time, 3 Data

// data sent to the link
pred sendData[t, t': Time] {
	t.sstate in WaitForCallFromAbove
	t'.sstate in WaitForACKorNAK
	t.sstate.seg1 = t'.sstate.seg2
	t.rstate = t'.rstate
	t.to = none
	t.back = none
	t'.back = none
	one d : t.sbuffer | {
		make_pkt[t.sstate.seg1, d, t'.to]
		t.sbuffer - d = t'.sbuffer
		t'.lastData = d
	}
	t.rbuffer = t'.rbuffer
}
run sendData for 3 but 2 Time

// date recieved from the link
pred recieveData[t, t': Time] {
	t.sstate = t'.sstate
	t.to != none
	t'.to = none
	t.back = none
	t'.lastData = t.lastData
	let p = t.to | {
		p.NOTcorrupt[] => (
			p.seg = t.rstate.seg3 => (
				t.rstate.seg3 != t'.rstate.seg3 and
				t.rbuffer + p.data = t'.rbuffer and
				make_pkt[p.seg, ACK, t'.back]
			) else (
				t.rstate.seg3 = t'.rstate.seg3 and
				t.rbuffer = t'.rbuffer and
				make_pkt[p.seg, ACK, t'.back]
			)
		) else (
			t.rstate.seg3 = t'.rstate.seg3 and
			t.rbuffer = t'.rbuffer and
			make_pkt[p.seg, NAK, t'.back]
		)
	}
	t.sbuffer = t'.sbuffer
}
run recieveData for 3 but 2 Time

// date recieved from the link
pred recieveACK[t, t': Time] {
	t.sstate in WaitForACKorNAK
	t.to = none
	t.back != none
	t'.back = none
	let p = t.back | {
		// did not check corruption here
		(p.NOTcorrupt[] and p.isACK[]) => (
			t'.to = none and
        	t.sstate.seg2.nextSeg[] = t'.sstate.seg1 and
			t'.lastData = none
		) else (
			t.sstate = t'.sstate and
			make_pkt[	t.sstate.seg2, t.lastData, t'.to] and
			t'.lastData = t.lastData
		)
	}
	t.sbuffer = t'.sbuffer
	t.rbuffer = t'.rbuffer
}
run recieveACK for 3 but 2 Time

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
	recieveACK[t, t'] or
	recieveData[t, t']
}

// traces of the system
pred traces {
	first[].init[]
	all t : Time - last[] | transition[t, t.next[]]  // or corruptData[t, t.next[]]
// extra constraint to make sure it does not corrput all the time
//	all t : Time - last[] - last[].prev[] | corruptData[t, t.next[]] => not corruptData[t.next[], t.next[].next[]]
}

pred possibleReliabe {
	traces	
//	some t : Time - last[] | sendData[t, t.next[]]
//	some t : Time - last[] | recieveACK[t, t.next[]]
//	some t : Time - last[] | recieveData[t, t.next[]]
//	some t : Time | t.end[]
}
run possibleReliabe for 10 but 4 Time, exactly 1 RealData

assert alwaysReliable {
	traces =>	last[].end[]
}

// check alwaysReliable  for 5 but exactly 8 Time, 1 RealData


//M1:Comment
// produce a counter example, because there is not enough time elapsed

// produces no counter example, because all packets eventually arrive
//check alwaysReliable  for 5 but exactly 11 Time, 5 RealData

