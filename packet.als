module packet

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
	checksum: CheckSum
}

pred make_pkt[d : Data, p : Packet] {
	p.data = d
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
