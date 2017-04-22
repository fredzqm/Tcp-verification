module RTD10
open util/ordering[Time]
open sender
open reciever
open link

sig Time {
	sender: Sender,
	reciever: Reciever,
	link: Link
}

pred Time.init[]{
	this.sender.init[]
	this.link.empty[]
	this.reciever.init[]
}
run init for 3 but 1 Time

pred Time.end[]{
	this.sender.end[]
	this.link.empty[]
	this.reciever.end[]
}

run end for 3 but 1 Time
