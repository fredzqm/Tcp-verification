module RTD10
open util/ordering[Time]
open sender
open receiver
open link
open packet

sig Time {
	sender: Sender,
	receiver: Receiver,
	link: Link
}


pred Time.init[]{
	this.sender.init[]
	this.link.empty[]	
	this.receiver.init[]
}
run init for 3 but 1 Time

pred Time.end[]{
	this.sender.end[]
	this.link.empty[]
	this.receiver.end[]
}
run end for 3 but 1 Time

pred transition[t, t': Time] {
	rdt_send[t.sender, t'.sender, t.link, t'.link]
	or rdt_rcv[t.receiver, t'.receiver, t.link, t'.link]
}

pred traces {
	first[].init[]
	all t : Time - last[] | transition[t, t.next[]]
	last[].end[]
}


run traces for 3 but 2 Data, 2 Packet


