
one sig TrackMe {

}

sig IndividualPermission {

allowedPermission: User -> ThirdParty

}

sig Sex, Address {}

sig User {

age: one Int,
address: one Address,
sex: one Sex,
ThirdPartiesPermissions:  set ThirdParty

}

one sig Data4Help {

users: set User,
thirdParties: set ThirdParty

}

abstract sig ThirdParty {

clients: set User

}

one sig AutomatedSOS extends ThirdParty {

}

one sig Track4Run extends ThirdParty {

}
