#------------------------------------------------------------------------#
# Optimization model No 3 Machining schedule and Feasibility problem of the multi task cell,
# Ph D project
# Karin Thörnblad february 2010

#=========================================================================#

# SETS #
		
param maxjobs;					# total amount of jobs
set JOBS := 1..maxjobs;			# Set of jobs
set I_OP;						# Largest set of operations (1 to the largest amount of operations for a job (8))
param n {JOBS};					# amount of operations for a job
set ACTIVE_I{j in JOBS} := setof {i in 1..n[j]}(i);	# every i go from 1,...,n(j) for each job
set K_RESOURCES ordered;		# Set of resources
set K_mach_RESOURCES ordered;	# Set of machining resources
set Q_PREC ordered;				# Set (j_prec) of jobs preceding q_follow(j_prec) for the same part
								# (j_prec,q_follow(j_prec)) form together the set Q in the math model
								
#---------------------------------------#
# PARAMETERS #

param w;						# transport time
param proc_time {I_OP,JOBS};	# processing time
param proc_time_mach {JOBS};	# processing time for the machining operation
param lambda {I_OP,JOBS,K_RESOURCES};	# flexibility matrix
param lambda_mach {JOBS,K_mach_RESOURCES};	# flexibility matrix for the machining problem
param r {JOBS};					# release date
param r_mach {JOBS};			# release dates for the machining problem
param d {JOBS};					# due date
# param d_mach {JOBS};			# due date for the machining problem (corrected with the remaining operations and internal transports after the machining operation)
param a {K_RESOURCES};			# time when resource is first available
param q_follow {Q_PREC};		# the second member of the pairs that form set Q for v_jq
param v_jq {Q_PREC};			# planned interoperation time
param v_mach_jq {Q_PREC};		# planned interoperation time for the MTC route operations between job j and q (of set Q)
param M;						# large number
param y_mach_solution{JOBS,JOBS,K_RESOURCES};	# the solution to the machining problem is to be fixed as y_2j2qk for the feasibility problem
param z_mach_solution{JOBS,K_RESOURCES};	# the solution to the machining problem is to be fixed as z_2jk for the feasibility problem
#param t_mach_solution{JOBS};	# the solution to the machining problem is to be fixed as t_2j for the feasibility problem
# param old_objective;			# In order to compare with the objective from the MTC2-model
param proc_tardi_objective;		# The sum of the total processing times and tardiness (no need for a small weight on t[1,j] since t[2,j] is fixed in the feas model
param p_postmach{JOBS};			# The sum processing and transport times for the operations no 3--n_j
								# Reason: To get the machining model objective as close to the MTC2 objective as possible
param resource_weight{K_RESOURCES};	# weight for the resources in order to avoid symmetries

#---------------------------------------#
# VARIABLES #

var t {I_OP,JOBS} >= 0; 	  	# variable starting time
var t_mach {JOBS} >= 0; 	  	# variable starting time for the machining problem
var z {I_OP,JOBS,K_RESOURCES} binary;  				# variable machine allocation
var z_mach {JOBS,K_mach_RESOURCES} binary;  		# variable machine allocation for the machining problem
var y {I_OP,JOBS,I_OP,JOBS,K_RESOURCES} binary; 	# variable for operation ordering in same resource
var y_mach {JOBS,JOBS,K_mach_RESOURCES} binary; 	# variable for operation ordering in same resource for the machining problem
var s {JOBS} >= 0;	  	  		# variable completion time
var s_mach {JOBS} >= 0;	  	  	# variable completion time for the machining problem
var h {JOBS} >= 0;	  	  		# variable tardiness
var h_mach {JOBS} >= 0;	  	  	# variable tardiness for the machining problem

#---------------------------------------#
# OBJECTIVES #

# Machining problem objective:
minimize Finish_times_and_tardiness_mach:
sum {j in JOBS} (s_mach[j]+ h_mach[j]);	#minimize job finish times and total tardiness

# Feasibility problem objective
minimize Process_times_and_tardiness_feas:
sum {j in JOBS} (s[j]-0.001*t[1,j]+h[j] + sum {i in ACTIVE_I[j], k in K_RESOURCES} resource_weight[k]*z[i,j,k]);	

#---------------------------------------#
# CONSTRAINTS #
   
# One operation is performed once and only once for the feasibility problem, if zero, the job has not been scheduled
subject to opconstraints_feas {j in JOBS,i in ACTIVE_I[j]}:
   sum {k in K_RESOURCES} z[i,j,k] = 1;

# One job is performed once and only once for the machining problem
subject to opconstraints_mach {j in JOBS}:
   sum {k in K_mach_RESOURCES} z_mach[j,k] = 1;

# Each operation is scheduled to an allowed resource
subject to flexconstraints {j in JOBS,i in ACTIVE_I[j], k in K_RESOURCES}:
   z[i,j,k] <= lambda[i,j,k];

# Each operation is scheduled to an allowed resource for the machining problem
subject to flexconstraints_mach {j in JOBS, k in K_mach_RESOURCES}:
   z_mach[j,k] <= lambda_mach[j,k];

# Both y cannot be 1 for two different operations scheduled to the same machine
subject to both_y_not_1_constraints {j in JOBS, q in JOBS, i in ACTIVE_I[j], p in ACTIVE_I[q], k in K_RESOURCES}:
   y[i,j,p,q,k] + y[p,q,i,j,k] <= if (i=p and j=q) then 2 else z[i,j,k];
   
# Both y cannot be 1 for two different operations scheduled to the same machine for the machining problem
subject to both_y_not_1_constraints_mach {j in JOBS, q in JOBS, k in K_mach_RESOURCES}:
   y_mach[j,q,k] + y_mach[q,j,k] <= if (j=q) then 2 else z_mach[j,k];

# At least one y must be 1 for two different operations scheduled to the same machine
subject to at_least_one_y_constraints {j in JOBS, q in JOBS, i in ACTIVE_I[j], p in ACTIVE_I[q], k in K_RESOURCES}:
   y[i,j,p,q,k] + y[p,q,i,j,k] + 1 >= if (i=p and j=q)  then 0 else (z[i,j,k] + z[p,q,k]);

# At least one y must be 1 for two different operations scheduled to the same machine for the machining problem
subject to at_least_one_y_constraints_mach {j in JOBS, q in JOBS, k in K_mach_RESOURCES}:
   y_mach[j,q,k] + y_mach[q,j,k] + 1 >= if (j=q)  then 0 else (z_mach[j,k] + z_mach[q,k]);
   
# Earliest start when the operation scheduled before has been completed in the same resource
subject to earliest_start_constraints {j in JOBS, q in JOBS, i in ACTIVE_I[j], p in ACTIVE_I[q], k in K_RESOURCES}:
   t[i,j] + proc_time[i,j] - M*(1-y[i,j,p,q,k]) <= if (i=p and j=q)  then M else t[p,q]; 
   
# Earliest start when the operation scheduled before has been completed in the same resource for the machining problem
subject to earliest_start_constraints_mach {j in JOBS, q in JOBS, k in K_mach_RESOURCES}:
   t_mach[j] + proc_time_mach[j] - M*(1-y_mach[j,q,k]) <= if (j=q)  then M else t_mach[q]; 

# Operations in the same job must be scheduled in order and with the time to transport between the resources
subject to same_job_constraints {j in JOBS, i in 1..(n[j]-1)}:
   t[i,j] + proc_time[i,j] + w <= t[i+1,j];

# Starting constraints, release dates
subject to start_constraints1 {j in JOBS}:
   t[1,j] >= r[j];
   
# Starting constraints for the machining problem
subject to start_constraints1_mach {j in JOBS}:
   t_mach[j] >= r_mach[j];

# Starting constraints, resource availability
subject to start_constraints2 {j in JOBS, i in ACTIVE_I[j], k in K_RESOURCES}:
   t[i,j] >= a[k]*z[i,j,k];
   
# Starting constraints, resource availability for the machining problem
subject to start_constraints2_mach {j in JOBS, k in K_mach_RESOURCES}:
   t_mach[j] >= a[k]*z_mach[j,k];

# Define completion time
subject to completion_time_constraints {j in JOBS}:
   s[j] = t[n[j],j] + proc_time[n[j],j];
   
# Estimates the completion time for the machining problem (p_postmach is the optimal postprocessing time)
subject to completion_time_constraints_mach {j in JOBS}:
   s_mach[j] = t_mach[j] + proc_time_mach[j] + p_postmach[j];

# Constraints of planned interoperation time for same production order
subject to interop_time_constraints {j_prec in Q_PREC}:
   s[j_prec] + v_jq[j_prec] <= t[1,q_follow[j_prec]];
   
# Constraints of planned interoperation time for same production order for the machining problem
subject to interop_time_constraints_mach {j_prec in Q_PREC}:
   s_mach[j_prec] + v_mach_jq[j_prec] <= t_mach[q_follow[j_prec]];

# Define tardiness
subject to tardiness_constraints {j in JOBS}:
   h[j] >= s[j]-d[j];

# Define tardiness for the machining problem
subject to tardiness_constraints_mach {j in JOBS}:
   h_mach[j] >= s_mach[j]-d[j];
   
# The solution to the machining problem is fixed as y_2j2qk för the feasibility problem
subject to y_fixed_constraints_feas {j in JOBS, q in JOBS, k in K_RESOURCES}:
	y[2,j,2,q,k] = y_mach_solution[j,q,k]; 
   
# The solution to the machining problem is fixed as z_2jk for the feasibility problem
subject to z2_fixed_constraints_feas {j in JOBS, k in K_RESOURCES}:
   z[2,j,k] = z_mach_solution[j,k];

#-------------------------------------------------------------------------#


	 

