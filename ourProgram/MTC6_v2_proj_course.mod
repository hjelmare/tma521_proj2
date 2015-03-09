
param T_HORIZON;				# end of set T_ALL_INTERVALS (discrete M)		
param maxjobs;					# total amount of jobs
set JOBS := 1..maxjobs;			# Set of jobs
set I_OP;						# Largest set of operations (1 to the largest amount of operations for a job (8))
param n {JOBS};					# amount of operations for a job
set ACTIVE_I{j in JOBS} := setof {i in 1..n[j]}(i);	# every i go from 1,...,n(j) for each job
set K_RESOURCES ordered;		# Set of resources
set K_mach_RESOURCES ordered;	# Set of machining resources
set Q_PREC ordered;				# Set (j_prec) of jobs preceding q_follow(j_prec) for the same part
								# (j_prec,q_follow(j_prec)) form together the set Q in the math model
#set P_SAME_JOBS dimen 2;				# (j,q), set of pairs of jobs, where j and q are the same kind of jobs. j and q are ordered so that the release dates r_j =< r_q
set T_ALL_INTERVALS := 0..T_HORIZON;    # Set of all discrete time intervals
set ourSet := 0..1;
								
#---------------------------------------#
# KARINS PARAMETERS #

param proc_time {I_OP,JOBS};	# processing time
param lambda {I_OP,JOBS,K_RESOURCES};	# flexibility matrix
param r {JOBS};					# release date
param d {JOBS};					# due date
param a {K_RESOURCES};			# time when resource is first available
param q_follow {Q_PREC};		# the second member of the pairs that form set Q for v_jq
param v_jq {Q_PREC};			# planned interoperation time
param v_disc_jq_ext {Q_PREC};	# discrete planned interoperation time for the MTC route operations between start of machining operation (i=2) of job j
								# and start of machining operation (i=2) of job q (of set Q)
param z_disc_solution{JOBS,K_RESOURCES};	# the solution to the machining problem is to be fixed as z_2jk for the feasibility problem
#param old_objective;			# In order to compare with the objective from the MTC2-model
param proc_tardi_objective;		# The sum of the total processing times and tardiness (no need for a small weight on t[1,j] since t[2,j] is fixed in the feas model
param p_j_o_postmach_disc{JOBS};	# The sum processing and transport times for the operations no 2--n_j (i.e. machining operation included!!!)
								# Reason: To calculate the job finish time in order to compare with the due dates

param proc_time_mach {JOBS};	# processing time for the machining operation
param r_mach {JOBS};			# release dates for the machining problem
param v_mach_jq {Q_PREC};		# planned interoperation time for the MTC route operations between job j and q (of set Q)
param p_postmach{JOBS};			# The sum processing and transport times for the operations no 3--n_j
# SETS #
	
#---------------------------------------#
# OUR PARAMETERS #

param A; #Ändra denna?
param B;
param w;						# transport time
param lMax;
param l;
param p;
param proc_time_disc {JOBS};	# discrete processing time for the machining operation
param lambda_mach {JOBS,K_mach_RESOURCES};	# flexibility matrix for the machining problem
param r_disc {JOBS};			# discrete release dates for the machining problem
param d_disc {JOBS};			# discrete due date for the machining problem (corrected with the remaining operations and internal transports after the machining operation)
param a_disc {K_mach_RESOURCES}; # discrete time when resource is first available
param M;						# large number
param y_disc_solution{JOBS,JOBS,K_RESOURCES};	# the solution to the machining problem is to be fixed as y_2j2qk for the feasibility problem
param T_length_interval;		# Length (hours) of one interval
param resource_weight{K_RESOURCES};	# weight for the resources in order to avoid symmetries

#---------------------------------------#
# VARIABLES #

var pi {JOBS};
var gamma {K_mach_RESOURCES};
var pi2 {JOBS};
var gamma2 {K_mach_RESOURCES};
var x_nail {JOBS,K_mach_RESOURCES,T_ALL_INTERVALS, 1..100} binary;   # discrete "nail-variable"
var x{JOBS, K_mach_RESOURCES, T_ALL_INTERVALS} binary;
var tau {K_mach_RESOURCES, 1..100} >= 0;

var final_tau {K_mach_RESOURCES, 1..lMax} binary;

#---------------------------------------#
# OBJECTIVES #
# Discrete dual restricted problem
maximize restricted_master_dual:
  sum{j in JOBS}(pi[j]) + sum{k in K_mach_RESOURCES}(gamma[k]);

# Column generation subproblem
minimize column_generation_subproblem{k in K_mach_RESOURCES}:
  sum{j in JOBS, u in T_ALL_INTERVALS}( (A*(u + proc_time_disc[j]) + B*max(u + proc_time_disc[j] - d_disc[j], 0 ) - pi[j])*x[j,k,u]  ) - gamma[k];


# LP relaxation of restricted master problem
minimize relaxed_restricted_master:
  sum {k in K_mach_RESOURCES, m in 1..lMax}( (sum{j in JOBS, u in T_ALL_INTERVALS}( (A*(u + proc_time_disc[j]) + B*(max(u + proc_time_disc[j] - d_disc[j], 0)))*x_nail[j,k,u,m] ))*tau[k,m] );



# LP final restricted master problem
minimize final_relaxed_restricted_master:
  sum {k in K_mach_RESOURCES, m in 1..lMax}( (sum{j in JOBS, u in T_ALL_INTERVALS}( (A*(u + proc_time_disc[j]) + B*(max(u + proc_time_disc[j] - d_disc[j], 0)))*x_nail[j,k,u,m] ))*final_tau[k,m] );
#------------------------------------------------------------#
#-------Constraints for restricted master problem------------#

subject to constraint2 {j in JOBS}:
  sum{k in K_mach_RESOURCES, m in 1..lMax}((sum{u in T_ALL_INTERVALS}(x_nail[j,k,u,m]))*tau[k,m] ) = 1;

subject to constraint3 {k in K_mach_RESOURCES}:
  sum{m in 1..lMax}(tau[k,m]) = 1;

#------------------------------------------------------------#
#------Constraints for column generation (subprob)-----------#

# Each operation is scheduled to an allowed resource for the machining problem
subject to flexconstraints_disc {k in K_mach_RESOURCES, j in JOBS}:
   sum {u in T_ALL_INTERVALS} x[j,k,u] <= lambda_mach[j,k];

# Resource k can only process one job at a time
subject to not_same_time_constr_disc {k in K_mach_RESOURCES, u in T_ALL_INTERVALS}:   
   sum{j in JOBS, v in max(u-proc_time_disc[j]+1,0)..u} (x[j,k,v]) <= 1;

# Starting constraints for the discrete machining problem
subject to start_constraints1_disc {k in K_mach_RESOURCES, j in JOBS, u in 0..(a[k] - 1)}:
   x[j,k,u] = 0;

#------------------------------------------------------------#
#-----Constraints to restricted master dual------------------#

#NOT USED
subject to constraint1{ m in 1..lMax, k in K_mach_RESOURCES}:
  sum{j in JOBS}( (sum{u in T_ALL_INTERVALS}(x_nail[j,k,u,m]))*pi[j]) + gamma[k] <= sum{j in JOBS, u in T_ALL_INTERVALS}((A*(u+proc_time_disc[j]) + B*(max(u + proc_time_disc[j] - d_disc[j], 0)))*x_nail[j,k,u,m]);

#-----------------------------------------------------------#
#---Constraints to final_relaxed restricted_master----------#

subject to final_constraint2 {j in JOBS}:
  sum{k in K_mach_RESOURCES, m in 1..lMax}((sum{u in T_ALL_INTERVALS}(x_nail[j,k,u,m]))*final_tau[k,m] ) = 1;

subject to final_constraint3 {k in K_mach_RESOURCES}:
  sum{m in 1..lMax}(final_tau[k,m]) = 1;


