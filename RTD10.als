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

