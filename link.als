module link
open packet

sig Link {
	packets: set Packet
}

pred udt_send[l, l': Link, p : Packet] {
	p not in l.packets
	l.packets + p = l'.packets
}

pred udt_rcv[l, l': Link, p : Packet] {
	p in l.packets
	l.packets - p = l'.packets
}

pred Link.empty[] {
	this.packets = none
}
run empty
