open util/relation
open util/integer

sig User {
dataFor: set ThirdParty,
health:one Int
} { health >=0 and health <= 4}

sig GroupOfUsers {
targetUsers: set User
}{#targetUsers > 0}

sig ThirdParty {
individualDataFrom: set User,
anonymizedDataFrom: set GroupOfUsers
}

one sig AutomatedSOS extends ThirdParty {
	emergency: set User
}

one sig Track4Run extends ThirdParty {
runs: set Run 
}

sig Run{
runners: some User,
spectators: set User,
time:one Int
}{(all r: Run | r in Track4Run.runs) and time >= 0 and time <= 6 }


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

	one ip:IndividualPermission | ip.status = ACCEPTED and ip.user = u' and ip.thirdParty = tp'
}

--AutomatedSOS

fact userInEmergencyCondition {
	all u:AutomatedSOS.individualDataFrom | (u.health < 3  iff u in AutomatedSOS.emergency) 
}

fact onlyAutomatedSOSUserCouldBeInEmergency {
	AutomatedSOS.emergency in AutomatedSOS.individualDataFrom
}

pred isUserSafe[u:User] {
	!(u.health < 3)
}

pred userIsNotSafe[u,u':User] {
	u'.health = minus[u.health,2]
}

pred userEnterInEmergencySituation[u,u':User] {
	u in AutomatedSOS.individualDataFrom
	u' in AutomatedSOS.individualDataFrom
	isUserSafe[u]
	!(u in AutomatedSOS.emergency)

	userIsNotSafe[u,u']
	(u' in AutomatedSOS.emergency)
}

--Track4Run

fact noAnonymousPermissionAutomatedTrack4Run{
	no ap:AnonymousPermission | ap.thirdParty = AutomatedSOS or ap.thirdParty = Track4Run 
}

fact noSameUserIsRunnerAndSpectatorsInSameRun{
all r: Run | no u: User | u in r.runners and u in r.spectators
}

fact onlyTrack4RunUserCanBeRunnerOrSpectators{
all u: User | (some r: Run | (u in r.runners or u in r.spectators ) ) implies u in Track4Run.individualDataFrom
}

fact noUserInTwoRunEventsAt{
	no u:User | some disj r1,r2:Run | (u in r1.runners or u in r1.spectators) and (u in r2.runners or u in r2.spectators) and r1.time = r2.time
}

pred addRunner[r,r':Run, ru:User]{
	r'.runners = r.runners + ru
}

pred addSpectator[r,r':Run, s:User]{
	r'.spectators = r.spectators + s
}

pred addSpectatorAndRunnerToARun[r,r':Run, s,s',ru,ru':User]{
	!(s in r.spectators or ru in r.runners)
	addRunner[r,r',ru]
	addSpectator[r,r',s]

	!(ru in r'.spectators or s in r'.runners)
}

assert noRunnerInTwoRunAtSameTime{
	all u:User | all disj r1,r2:Run | !(u in r1.runners  and u in r2.runners and r1.time = r2.time)
}


pred show {
	some u:User| u in AutomatedSOS.emergency 
	some ip:IndividualPermission | ip.status = ACCEPTED 
	some ap:AnonymousPermission |ap.status = ACCEPTED
	some r:Run | #r.runners>0 and #r.runners<3 and #r.spectators>0 and #r.spectators<3
}

run show for 5 but 4 AnonymousPermission, 4 IndividualPermission, 3 ThirdParty,5 User
run addIndividualPermission
run  userEnterInEmergencySituation
run addSpectatorAndRunnerToARun
check noRunnerInTwoRunAtSameTime for 5










