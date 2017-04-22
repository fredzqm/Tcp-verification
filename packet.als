module packet

sig Data {}

sig Packet {
	data: Data
}

pred make_pkt[d : Data, p : Packet] {
	p.data = d
}

pred extract[p : Packet, d : Data] {
	p.data = d
}
