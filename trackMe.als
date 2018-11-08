open util/relation

sig User {
allowedThirdParties: set ThirdParty
}

sig GroupOfUsers {
filteredUsers: set User
}

one sig Data4Help {
anonymousSubscription: set AnonymousPermission,
individual: set IndividualPermission,
anonymousOneTime: set AnonymousPermission
}

sig ThirdParty {
allowedIndividual: set User,
allowedAnonymazed: set GroupOfUsers
}

one sig AutomatedSOS extends ThirdParty {}

one sig Track4Run extends ThirdParty {}

abstract sig RequestStatus {}
one sig ACCEPTED extends RequestStatus {}
one sig REFUSED extends RequestStatus {}
one sig UNDEFINED extends RequestStatus{}

sig IndividualPermission {
individualPermission: ThirdParty -> User,
status: one RequestStatus
}{ #individualPermission = 1 }

sig AnonymousPermission {
anonymousPermission: ThirdParty -> GroupOfUsers,
status: one  RequestStatus
}


-- anonymous/subscription facts

fact distinctUsersInAGroup {
all gu: GroupOfUsers, u1: User, u2: User | u1 in gu.filteredUsers and u2 in gu.filteredUsers and u1!=u2
}

fact anonymousSingleRequestCondition {
(all ap: AnonymousPermission | ap.status = ACCEPTED implies #ThirdParty.(ap.anonymousPermission) > 1000) and
(all ap: AnonymousPermission |  ap.status =REFUSED implies #ThirdParty.(ap.anonymousPermission) <= 1000)
}

fact {
all ap:AnonymousPermission | (ap in Data4Help.anonymousSubscription or ap in Data4Help.anonymousOneTime) implies (ap.status = ACCEPTED or ap.status = REFUSED)
}

fact {
all tp: ThirdParty, gu: GroupOfUsers | gu in tp.allowedAnonymazed iff 
( one ap: AnonymousPermission | ap in Data4Help.anonymousSubscription and ap.status = ACCEPTED and (tp in dom[ap.anonymousPermission] and gu in ThirdParty.(ap.anonymousPermission)) )
}

fact {
all gu: GroupOfUsers | some ap: AnonymousPermission | gu in ThirdParty.(ap.anonymousPermission)
}

-- individual facts

fact {
all u1,u2: User, tp: ThirdParty | (u1 in tp.allowedIndividual and u2  in tp.allowedIndividual) implies u1 != u2
}

fact {
all u: User, tp1,tp2: ThirdParty | (tp1 in u.allowedThirdParties and tp1 in u.allowedThirdParties) implies tp1 != tp2
}

fact individualRequestCondition{
all pi: IndividualPermission | pi in Data4Help.individual and (pi.status = ACCEPTED or  pi.status = REFUSED)
}

fact b {
(all tp:ThirdParty, u: User | tp in u.allowedThirdParties and u in tp.allowedIndividual iff 
(one ip:IndividualPermission | tp in dom[ip.individualPermission] and ThirdParty.(ip.individualPermission) = u and ip.status = ACCEPTED))
	and 
	( all tp:ThirdParty, u: User | !(tp in u.allowedThirdParties and u in tp.allowedIndividual)  iff
	 (no ip:IndividualPermission | (tp in dom[ip.individualPermission] and ThirdParty.(ip.individualPermission) = u)) )
}


pred notAlreadyExistingIndividualPermission [ ip: IndividualPermission, u: User, tp: ThirdParty]{
	no ip1: IndividualPermission in Data4Help.allowedIndividual | ThirdParty.(tp1.individualPermission) = u and dom[ip1.individualPermission] = tp
}

pred individualPermissionAl[ip: IndividualPermission, tp: ThirdParty, u: User] {
	(no (ip in Data4Help.individual and ip.status = ACCEPTED)) and
	!(u in tp.allowedIndividual or tp in u.allowedThirdParties)
}

pred createAnIndividualPermission[ip: IndividualPermission, tp: ThirdParty, u: User] {
	--preconditions
	individualPermissionNotAlreadyAccepeted(ip,tp,u),
	
}










