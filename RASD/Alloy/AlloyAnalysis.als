abstract sig User{}

sig Citizen extends User{
	person: Person
}

sig Authority extends User{
	knownPermissions: set Plate->PERMISSION
}

sig Person{
	cars: set Car
}

sig Violation{
	type: VIOL_TYPE,
	pic: Picture,
	date: Date,
	time: Time,
	pos: Position
}

sig Ticket{
	releasedBy: Authority,
	viol: Violation,
	plate: Plate
}

sig Car{
	plate: one Plate	//A2
}
sig Plate{
	permissions: set PERMISSION
}
sig Date{}
sig Time{}
sig Position{}
sig Picture{
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

assert G5{
	no t: Ticket | t.viol.type.permission in t.plate.permissions
}

assert G6{
	all v: Violation | (not v.type.permission in v.pic.plate.permissions) 
				implies
				(some t:Ticket | t.viol  = v)
}

fact A1{
	no disj c1,c2: Car | c1.plate = c2.plate
}

fact A3{
	no c: Car | some disj p1,p2: Person | c in p1.cars and c in p2.cars
}

fact A4{
	all t: Ticket | t.plate.permissions in t.releasedBy.knownPermissions[t.plate]
}

check G5
check G6
