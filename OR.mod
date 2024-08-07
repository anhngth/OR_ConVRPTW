int numCustomer = 20; 	// Number of customers
int numDay      = 10; 	// Planning horizon
int numVehicle  = 10; 	// Number of Vehicle
int C = 800; 			// Capacity per Vehicle, unit: kg
int T = 360; 			// Total working time a day, unit: minute

range N = 0..numCustomer; 	// Customer + depot at 0
range D = 1..numDay; 		// Index of the day
range K = 1..numVehicle; 	// Index of the vehicle

float q[N][D]=...; 			// Demand of Customer i on Day d
float dist[N][N]=...; 		// Distance matrix
float t[N][N]=...; 			// Travel time matrix

int s[N]=...; 				// Service time of customer i
int l[N]=...; 				// Lower bound of the time window of customer i
int u[N]=...; 				// Upper bound of the time window of customer i
int w[N][D]=...; 			// = 1 if customer i requires service on day d, and 0 otherwise

dvar boolean x[N][N][K][D]; 	// Equal 1 if arc (i, j) is traversed by vehicle k on day d, and 0 otherwise
dvar boolean y[N][K][D]; 		// = 1 if customer i is is assigned to vehicle k on day d, and 0 otherwise
dvar boolean z[K]; 				// = 1 if vehicle k is used in any day of the planning horizon, and 0 otherwise
dvar float+ a[N][D]; 			// Start time
dvar float+ e[N][D]; 			// Waiting time
dvar int+ alt[N][K][D]; 		// Auxiliary variable for linear transformation
dvar float+ alt2[N][N][K][D];	// Auxiliary variable for linear transformation

minimize sum(k in K) z[k];

subject to {
	Constraint_1: //Each customer is serviced on each day they require service
	forall (i in N : i != 0, d in D)
	  sum (k in K) (y[i][k][d]) == w[i][d];
	
	Constraint_2a: //Transfer to linear equation
	forall (k in K, d in D, i in N) {
	  (y[i][k][d] == 0) => (alt[i][k][d] == 0);
	  (y[i][k][d] == 1) => (alt[i][k][d] == q[i][d]);
	}	
	
	Constraint_2: // Ensure that the vehicle capacity is not exceeded
	forall (k in K, d in D)
	  sum (i in N : i != 0) (alt[i][k][d]) <= C;
	
	Constraint_3: // Ensure that if customer i is served by vehicle k on the day d, then vehicle k must be used during the planning horizon
	forall (i in N : i != 0, d in D, k in K)
	  z[k] >= y[i][k][d];
	  
	Constraint_4: // Ensure that all assigned customers have exactly one predecessor and one successor
	forall (j in N : j != 0, k in K, d in D) {
	  sum (i in N : i != j) (x[i][j][k][d]) == sum (i in N : i != j)(x[j][i][k][d]);
	  sum (i in N : i != j) (x[j][i][k][d]) == y[j][k][d];
	}
	  	 
	Constraint_5: // The vehicle must start and end his route in a depot
	forall(k in K, d in D) {
	  sum (j in N : j != 0) x[0][j][k][d] == sum(i in N : i != 0) x[i][0][k][d];
	  sum (i in N: i != 0) x[i][0][k][d] == z[k];
	}	

	Constraint_6:
	forall (i in N : i != 0, alpha in D, beta in D, k in K : alpha != beta)
	  w[i][alpha] + w[i][beta] - 2 <= y[i][k][alpha] - y[i][k][beta];

	Constraint_7a: // Transfer to linear
	forall (i in N, j in N : j!= 0 && i != j, k in K, d in D) { 
	  (x[i][j][k][d] == 0) => (alt2[i][j][k][d] == 0);
	  (x[i][j][k][d] == 1) => (alt2[i][j][k][d] == s[i] +t[i][j] + e[j][d]);
	}
	
	Constraint_7:
	forall (i in N, j in N : j!= 0 && i != j, k in K, d in D)
	  a[i][d] + alt2[i][j][k][d] - (1 - x[i][j][k][d])*T <= a[j][d];
	
	Constraint_8: //Cons (7) and (8) set the service start-times at the customers’ sites, the arrival times for two customers are related
	forall (i in N, j in N : j!= 0 && i != j, k in K, d in D)
	  a[i][d] + alt2[i][j][k][d] + (1 - x[i][j][k][d])*T >= a[j][d];
	  
	Constraint_9: // Enforce that vehicles return to the depot on time
	forall (i in N : i != 0, d in D)
	  a[i][d] + s[i] + t[i][0] <= T;
	
	Constraint_10: // The time windows of the customers are enforced by inequalities
	forall (i in N, d in D) {
	  l[i]*w[i][d] <= a[i][d];
	  a[i][d] <= u[i] * w[i][d];
	}
}
	  
