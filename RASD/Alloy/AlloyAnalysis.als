open util/boolean

abstract sig User{
	visibleViolations: set Violation
}

sig Citizen extends User{
	person: Person
}

sig Authority extends User{
	knownPermissions: set Plate->PERMISSION	//The permissions SafeStreets knows about
}

sig Person{
	cars: set Car
}

sig Violation{
	type: VIOL_TYPE,
	data: set Data,
	modified: Bool
}{
	//(some disj d1,d2:Data | d1.type = d2.type) implies (modified = True) and	//Different data iff something has been modified
	#data>0
}

sig Ticket{
	releasedBy: Authority,
	viol: Violation,
	plate: Plate
}{
	viol in releasedBy.visibleViolations	//Can't make a ticket from a violation you cannot access
}

sig Car{
	plate: one Plate	//A2: Each car exactly has 1 plate
}
sig Plate{
	permissions: set PERMISSION
}
abstract sig Data{}{
	no disj v1,v2: Violation | v1.data = v2.data	//non-obiquity
}
sig Date extends Data{}
sig Time extends Data{}
sig Position extends Data{}
sig Picture extends Data{
	plate: Plate
}

sig Statictics{
	from: some Violation
}

abstract sig VIOL_TYPE{
	permission: lone PERMISSION
}{}
one sig onBycicleLane extends VIOL_TYPE{}{permission = none}
one sig onSidewalk extends VIOL_TYPE{}{permission = none}
one sig onDisabledParking extends VIOL_TYPE{}{permission = disabledPermission}

abstract sig PERMISSION{}
one sig disabledPermission extends PERMISSION{}
//GOALS
//G3 Prevent the autorities to have to manually address parking tickets => not defined in the model
//G7 Allow both citizens and authorities retrive informations about previous violations and released tickets, possibly in an aggregated form 
assert G1{//Allow citizens to notify parking violations
	//?
}

assert G2{//Allow citizens to provide all the needed data about violation, in particular infraction type, picture, date, time and position
	//?
}

assert G3{//Prevent the autorities to have to manually address parking tickets
	//?
}

assert G4{//Ensure no tickets can be emitted if the notification's data has been modified somehow
	no t: Ticket | t.viol.modified = True
}
assert G5{//Ensure no tickets can be emitted if the plate of the car that committed the infringment owns a permission for that infringiment
	no t: Ticket | t.viol.type.permission in t.plate.permissions
}

assert G6{// Every notification not covered by \ref{G_discardAltered} or \ref{G_respectPermissions} will always be saved (In this analysis, assume that every saved violation generates a ticket)
	all v: Violation | (v.modified = False and some pic: Picture | pic in v.data and not (v.type.permission in pic.plate.permissions)) implies 
	some t:Ticket | t.viol = v	
}


//PROGRAMMING FUNCTIONS
pred insertData[c:Citizen,v:Violation,d:Data]{

}

//ALLOY FUNCTIONS AND PREDICATES
pred fullData[v:Violation]{
	(some d:Date | d in v.data) and
	(some d:Time | d in v.data) and
	(some d:Position | d in v.data) and
	(some d:Picture | d in v.data)
}


//DOMAIN ASSUMPTIONS
fact A1{	//Different cars always have different plates
	no disj c1,c2: Car | c1.plate = c2.plate
}

fact A3{//No car is owned by more than 1 person
	no c: Car | some disj p1,p2: Person | c in p1.cars and c in p2.cars
}

fact A4{//SafeStreets will have access to any permission released by the auths
	all per: PERMISSION, p:Plate |
		(per in p.permissions) implies (some a: Authority | a.knownPermissions[p] = per)	//valid syntax?
}


//CONSTRAINTS
assert C1{//The authorities will not be able to register automatically to the service. For authentication, they'll be verified and added by an administrator of the system
	
}
//REQUIREMENTS
//R4: For each data to insert, if the  user's device has a sensor to collect thatkind of data, that sensor should be used instead of manual insertion (example: GPS)
//R5: The system should notify the user when his notification has been processed correctly, or ask for more datailed data (example: a more focused picture) if needed.

fact R1{	//Requires the authorities to give SafeStreets access to the tickets they emitted using SafeStreets' data
	no t: Ticket | t.plate.permissions in t.releasedBy.knownPermissions[t.plate]
}


fact R2{	//To define better
//	Automatically extract the plate number of the car from the photo, ignoring cars in the background if present
}

fact R3{	//Ensure no data is altered from the insertion to the eventual storage
	all v: Violation | (v.modified = True) implies (no u: User | v in u.visibleViolations)	//no user can "see" it->it's not stored
}
fact R6{//R6: If a notification is missing any needed data, the client application will prevent the user from sending them
	//no v:Violation | not fullData[v]
}

fact tmp{#Violation > 0}

//check G3 for 10
check G4
check G5
check G6
