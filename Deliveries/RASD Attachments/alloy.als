

abstract sig User{}
enum Gender{M,F}

sig string,boolean{}

sig Date{
   Day: one Int,
   Month: one Int,
   Year: one Int
}

sig RegisteredUser extends User{
  Username: one string,
  Password: one string,
  Name: one string,
  Surname: one string,
  Email: one string,
  Gender: one Gender,
  BirthDate: one Date,
  HouseAddress: lone string,
  MobileNumber: one string
}

sig OccasionalUser extends User{
   ID: one Int
}

sig Taxi {
  ID: one Int,
  Position : set string,
  //vedere se si può togliere
  TaxiZone: one Zone
}

sig TaxiDriver extends  RegisteredUser{
       taxi: one Taxi,
       HiringDate: one Date,
       Available: one boolean,
       reservations: some IstantaneousReservation
}

sig Customer extends RegisteredUser{
       reservations: some Reservation,
}

sig SpecialUser extends RegisteredUser{
 HiringDate: one Date
}


abstract sig Reservation {
   ID: one Int,
   ResDate: one Date,
   SourceAddress: one string,
   DestinationAddress: one string,
}

sig IstantaneousReservation extends Reservation{
}

sig FutureReservation extends Reservation{
}

sig Zone{
   ID: one Int,
   TaxiQueue: set Taxi
}

sig Map
{
    zones: some Zone
}

sig Payment{
  Price: one Int
}

abstract sig Ride{
  ID: one Int,
  paymentInfo: one Payment
}

sig ReservedRide extends Ride
{
     associatedReservation: one IstantaneousReservation, 
}

sig OccasionalRide extends Ride
{
   takenBy: one OccasionalUser
}

//Vincoli 

//User
fact uniqueUserID{
no ru1,ru2: RegisteredUser | (ru1!=ru2 and ru1.Username=ru2.Username)
}

//Taxi Driver
fact oneTaxiToOneTaxiDriver{
no t1,t2: TaxiDriver | (t1!=t2 and t1.taxi=t2.taxi)
}


//Taxi - Taxi Driver
fact taxiAssociation{
#TaxiDriver = #Taxi
}


//Taxi

//unique ID
fact uniqueTaxiID{
no t1,t2: Taxi | (t1!=t2 and t1.ID=t2.ID)
}

fact postiveTaxiID{
no t1: Taxi | t1.ID<0
}

//states that a taxi must be included at least in one zone 
//fact oneTaxiInOneZone{


//no z1,z2: Zone, t1: Taxi | (z1.ID != z2.ID ) and t1.TaxiZone 

//}

//one taxi one zone (TODO)
//vedere con il prodotto cartesiano e le associazioni zona taxi
//BOZZA (rivedere
//fact oneTaxiOneZone{
//no z1,z2:Zone | (z1.ID!=z2.ID and (((z1.ID -> z1.TaxiQueue).~(z2.ID->z2.TaxiQueue)) != (none->none)))
//}

fact existsZoneForTaxi{
no t: Taxi,z1,z2:Zone | (z1!=z2) and (t in z1.TaxiQueue and t in z2.TaxiQueue)

}

//fact OneAtLeastZone{
//no t: Taxi | all z: Zone |( t not in z.TaxiQueue)
//}

//Zone

fact uniqueZoneID{
no z1,z2: Zone | (z1!=z2 and z1.ID=z2.ID) 
}

fact postiveZoneID{
no z1: Zone | z1.ID<0
}

//Occasional User
fact uniqueOccasionalUserID{
no ou1,ou2: OccasionalUser | (ou1!=ou2 and ou1.ID=ou2.ID)
}

fact postiveOccUserID{
no ou1: OccasionalUser | ou1.ID<0
}

//Ride

fact uniqueRideID{
no r1,r2: Ride| (r1!=r2 and r1.ID=r2.ID)
}

fact postiveRideID{
no r1: Ride | r1.ID<0
}

//Reservation

fact uniqueReservationID{
no r1,r2: Reservation| (r1!=r2 and r1.ID=r2.ID)
}

fact differentAddresses{
no r1: Reservation | r1.SourceAddress=r1.DestinationAddress
}

fact postiveReservationID{
no r1: Reservation| r1.ID<0
}


//Payment
fact PositivePrice{
no p1: Payment | p1.Price<0
}

//Date

//we suppose that february has always 28 days
fact validDate{
   no d1: Date | ( (d1.Month = 1 or d1.Month = 3 or d1.Month = 5 or d1.Month = 7 or d1.Month=10 or d1.Month=12) =>
       (d1.Day >0 and d1.Day <=31)) and ((d1.Month=4 or d1.Month=6 or d1.Month = 9 or d1.Month=11) => (d1.Day >0 and d1.Day<=30)) 
      and ((d1.Month=2) => (d1.Day>0 and d1.Day <=28)) and d1.Month>=1 and d1.Month<=12 and d1.Year>0 and d1.Day>0
      

}

fact noRideBeforeAssumption{
no t1: TaxiDriver, ir1: IstantaneousReservation | (ir1.ResDate.Year>t1.HiringDate.Year) or ((ir1.ResDate.Year = t1.HiringDate.Year) and (ir1.ResDate.Month>t1.HiringDate.Month))
or((ir1.ResDate.Year)=(t1.HiringDate.Year) and (ir1.ResDate.Month = t1.HiringDate.Month) and (ir1.ResDate.Day>t1.HiringDate.Day))

}



fact OneAtLeastZone{
no t: Taxi | (all z: Zone |( t not in z.TaxiQueue))
}


//assert noTwoRequestIdentical{
//no r1,r2: Reservation | r1.ID != r2.ID and r1.ResDate =r2.ResDate and r1.SourceAddress = r2.SourceAddress and r1.DestinationAddress = r2.DestinationAddress
//}

//check noTwoRequestIdentical

pred show(){
#TaxiDriver>1
#User>1
#Reservation >1
#Ride>1
}

run show for 3 but 2 TaxiDriver, 2 User


