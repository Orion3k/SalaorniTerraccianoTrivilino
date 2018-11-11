open util/relation

sig User {
dataFor: set ThirdParty,
health:one Int
} { health <= 7 and health >= 0}

sig GroupOfUsers {
targetUsers: set User
}{#targetUsers > 0}

sig ThirdParty {
individualDataFrom: set User,
anonymizedDataFrom: set GroupOfUsers
}

sig Ambulance{}

one sig AutomatedSOS extends ThirdParty {
	emergency: User -> lone Ambulance
}

abstract sig RequestStatus {}
one sig ACCEPTED extends RequestStatus {}
one sig REFUSED extends RequestStatus {}
one sig UNDEFINED extends RequestStatus{}

sig IndividualPermission {
thirdParty: one ThirdParty,
user: one User,
status: one RequestStatus
}

sig AnonymousPermission {
thirdParty: one ThirdParty,
group: one GroupOfUsers,
status: one  RequestStatus
}

--Data4Help

fact individualDataRequestCondition {
all ip: IndividualPermission | ip.status = ACCEPTED iff (ip.user in ip.thirdParty.individualDataFrom and ip.thirdParty in ip.user.dataFor )
}

fact toAcquireIndividualDataMustExistsAPermission{
all u: User, tp: ThirdParty | u in tp.individualDataFrom iff ( one ip : IndividualPermission | ip.user = u and ip.thirdParty = tp and ip.status = ACCEPTED )
}

fact oneToOnePermissionCondition{
	all u: User, tp: ThirdParty | u in tp.individualDataFrom iff tp in u.dataFor
}

fact notAcceptedPermissionAvoidDataExchange{
all ip: IndividualPermission | (ip.status = REFUSED or ip.status = UNDEFINED) iff !( ip.user in ip.thirdParty.individualDataFrom)
}

fact individualPermissionAreUnique{
no disj ip1, ip2 : IndividualPermission |  ip1.user = ip2.user and  ip1.thirdParty = ip2.thirdParty and !(ip1.status = UNDEFINED or ip2.status = UNDEFINED)
}

fact anonymazedPermissionCondition {
all ap: AnonymousPermission | (ap.status = ACCEPTED iff #ap.group.targetUsers > 1000) and ( ap.status = REFUSED iff #ap.group.targetUsers <= 1000  ) and !(ap.status = UNDEFINED)
}

fact groupExistsOnlyForAnonymazedPermissions {
all gu: GroupOfUsers | some ap: AnonymousPermission | ap.group = gu
}

fact toAcquireAnonymazedDataMustExistAPermission{
all gu: GroupOfUsers, tp : ThirdParty |  gu in tp.anonymizedDataFrom iff ( some ap: AnonymousPermission | ap.group = gu and ap.thirdParty = tp and ap.status = ACCEPTED )
}

fact anonymazedPermissionsAreUnique {
no disj ap1,ap2: AnonymousPermission | ap1.thirdParty = ap2.thirdParty and ap1.group = ap2.group
}

fact usersInGroupAreUnique {
all gu: GroupOfUsers | ( no disj u1,u2: User | u1 in gu.targetUsers and u2 in gu.targetUsers and u1 = u2 )
}

pred notExistsAnAcceptedIndividualPermission[u: User,tp: ThirdParty] {
	!(u in tp.individualDataFrom)
}

pred addUserToThirdParty[tp,tp':ThirdParty,u:User] {
	tp'.individualDataFrom = tp.individualDataFrom + u
}

pred addThirdPartyToUser[u,u':User, tp:ThirdParty] {
	u'.dataFor = u.dataFor + tp
}

pred addIndividualPermission[ u,u' : User, tp,tp' : ThirdParty] {

	notExistsAnAcceptedIndividualPermission[u, tp]

	addUserToThirdParty[tp,tp',u]
--	addThirdPartyToUser[u,u',tp]

	one ip:IndividualPermission | ip.status = ACCEPTED and ip.user = u' and ip.thirdParty = tp'
}

--AutomatedSOS

fact {
all u: User | u in dom[AutomatedSOS.emergency] implies u in AutomatedSOS.individualDataFrom
}

fact {
all u: User | u in dom[AutomatedSOS.emergency] implies u.health < 4
}

fact {
all u: User | ( u in AutomatedSOS.individualDataFrom and  u.health < 4) implies u in dom[AutomatedSOS.emergency]
}


pred isUserSafe[u:User] {
	u.health >= 2
}

pred userIsNotSafe[u,u':User] {
	u'.health = u.health - 2
}
pred userEnterInEmergencySituation[u,u':User] {
	isUserSafe[u]
	!(u in dom[AutomatedSOS.emergency])

	userIsNotSafe[u,u']
	(u' in dom[AutomatedSOS.emergency])

	
}

--Track4Run

one sig Track4Run extends ThirdParty {
runs: set Run 
}

sig Run{
runners: some User,
spectators: set User 
}{all r: Run | r in Track4Run.runs }

fact {
all r: Run | no u: User | u in r.runners and u in r.spectators
}

fact {
all u: User | (some r: Run | (u in r.runners or u in r.spectators ) ) implies u in Track4Run.individualDataFrom
}

pred show {
some u: User | u in dom[AutomatedSOS.emergency]
some u: User | u.health > 4  and u in AutomatedSOS.individualDataFrom
--#AutomatedSOS.individualDataFrom > 3
--#dom[AutomatedSOS.emergency] > 2
}

run show
--run show for 4 but 3 Run, 10 User, 0 ThirdParty

--run show for 5 but 4 AnonymousPermission, 4 IndividualPermission, 3 ThirdParty, 5 User
--run addIndividualPermission
--run  userEnterInEmergencySituation










