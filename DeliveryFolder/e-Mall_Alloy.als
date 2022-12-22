//SIGNATURES

sig Email {} { this in User.email}
sig Password {} {this in User.password}
sig UserCode {} {this in User.userCode}

sig User {
	email : one Email,
	password : one Password,
	userCode : one UserCode
}

sig Date{} {this in Booking.date}

sig TimeSlot{
	start : one Int,
	end : one Int 
}{start < end and start >= 0  and this in Booking.timeSlot}

sig Booking {
	user : one User,
	date : one Date,
	timeSlot : one TimeSlot,
	chargingSlot : one ChargingSlot
}{this in CPMS.bookings}

sig Address {}{this in ChargingStation.address}

sig ChargingSlot{}{this in ChargingStation.chargingSlots}

sig ChargingStation{
	address : one Address,
	chargingSlots : some ChargingSlot
}{#chargingSlots > 0 and this in CPO.chargingStations}

sig CPMS{
	bookings : set Booking
}{this in CPO.cpms}

sig CPO {
	chargingStations : some ChargingStation,
	cpms : one CPMS
}


//PREDICATE FOR FACTS

//Predicate for overlapping time slots
pred timesOverlap [ts1, ts2 : TimeSlot] {
	(ts2.start < ts1.start and ts1.start < ts2.end) or 
	( ts1.start < ts2.start and ts2.start < ts1.end) or 
	(ts1.start = ts2.start)
}


//FACTS

//USER

//One email per user
fact oneEmailPerUser {
	no disj u1, u2 : User | 
		u1.email = u2.email
}
//One usercode per user
fact oneCodePerUser {
	no disj u1, u2 : User | 
		u1.userCode= u2.userCode
}

//No overlaps for user 
fact userIsNotUbiquitous{
	all u : User | 
		no disj b1, b2 : Booking | 
			b1.user = u and 
			b2.user = u and 
			b1.date = b2.date and 
			timesOverlap[b1.timeSlot , b2.timeSlot]  
}

//BOOKINGS

//The slot of a booking needs to belong to the correct CPO
fact bookingsAreCoherent{
	no b : Booking | 
		some cpo : CPO | 
			b in cpo.cpms.bookings and 
			b.chargingSlot not in cpo.chargingStations.chargingSlots 
}

//A booking belongs to a single CPMS
fact {
	no disj cpms1, cpms2 : CPMS | 
		one b : Booking | 
			b in cpms1.bookings and b in cpms2.bookings
}

//No overlaps on date, timeslot, charging station and charging slot
fact noOverlapsInBooking {
	no disj b1, b2 : Booking | 
		b1.date = b2.date and 
		timesOverlap[b1.timeSlot, b2.timeSlot] and 
		b1.chargingSlot = b2.chargingSlot 
}


//CHARGING STATIONS & CHARGING SLOTS

//All stations belong to different CPOs
fact allStationsToDifferentCPO{
	no disj cpo1, cpo2 : CPO | 
		some chargingStation : ChargingStation | 
			chargingStation in cpo1.chargingStations and 
			chargingStation in cpo2.chargingStations
}

//All charging slots belong to a charging station
fact noSlotWithoutChargingStation{
	all slot : ChargingSlot | 
		one cs : ChargingStation | 
			slot in cs.chargingSlots			
}

//Each charging station has a unique address
fact noSameAddress {
	no disj cs1, cs2 : ChargingStation | 
		cs1.address = cs2.address
}

//The same slot cannot belong to two different charging stations
fact noSameSlots {
	no disj cs1, cs2 : ChargingStation | 
		some slot : ChargingSlot | 
			slot in cs1.chargingSlots and slot in cs2.chargingSlots
}


//CPO & CPMS

//All CPMS belong to different CPOs
fact allCPMSToDifferentCPO{
	no disj cpo1, cpo2 : CPO | 
		some cp: CPMS | 
			cp in cpo1.cpms and 
			cp in cpo2.cpms
}

//PREDICATES TO GENERATE WORLDS

//General World
pred generalWorld {
	#ChargingStation > 3
	#CPO > 2
	#Booking > 4
	#User > 1
}
run generalWorld for 10

//World where booking for same socket in same day has different timeslot
pred noOverbooking {
	#ChargingSlot = 1
	#Booking = 2
	#User = 2
	#Date = 1
}
run noOverbooking for 10

//World where a user can't have the same date  for two bookings in the same timeslot
pred noSamePlace {
	#TimeSlot = 1
	#User = 1
	#Booking = 3
}
run noSamePlace for 10

//World where there's a ChargingStation without any booking
pred emptyChargingStation{
	#Booking = 0
	#CPMS = 1
}
run emptyChargingStation for 10

//World where a user has no bookings
pred userWithNoBookings[u :User]{
	no b : Booking | b.user = u
	#Booking > 1
}
run userWithNoBookings for 10


