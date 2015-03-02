#------------------------------------------------------------------------#
# Optimization model No 6 Discrete machining and feasibility problem of the multi task cell,
# Ph D project
# Karin Thörnblad 2011
#
#-------------------------------------------------------------------------#
#	Difference from MTC4_v8.mod
#				Change of constraints interop_time_constraints_disc to a 
#				new version from Wolsey 1997 p. 163.
#
#================= Change history ========================================#
# 2011-04-11	Version MTC6_v2.mod created.
#				Reason: Test with new constraints 
#				Was before: not_same_time_new_constr_disc {j in JOBS, q in JOBS, k in K_mach_RESOURCES, u in 0..T_HORIZON}:   
#   			sum{v1 in max(u-proc_time_disc[j]+1,0)..u}x_nail[j,k,v1] + sum{v2 in max(u-proc_time_disc[q]+1,0)..u}x_nail[q,k,v2] <= if (j=q) then 2 else 1;
#				Now: subject to not_same_time_constr_disc {k in K_mach_RESOURCES, u in 0..T_HORIZON}:   
#   			sum{j in JOBS, v in max(u-proc_time_disc[j]+1,0)..u}x_nail[j,k,v] <= 1;
#
#=========================================================================#

# SETS #

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
								
#---------------------------------------#
# PARAMETERS #

param w;						# transport time
param proc_time {I_OP,JOBS};	# processing time
param proc_time_disc {JOBS};	# discrete processing time for the machining operation
param lambda {I_OP,JOBS,K_RESOURCES};	# flexibility matrix
param lambda_mach {JOBS,K_mach_RESOURCES};	# flexibility matrix for the machining problem
param r {JOBS};					# release date
param r_disc {JOBS};			# discrete release dates for the machining problem
param d {JOBS};					# due date
param d_disc {JOBS};			# discrete due date for the machining problem (corrected with the remaining operations and internal transports after the machining operation)
param a {K_RESOURCES};			# time when resource is first available
param a_disc {K_mach_RESOURCES}; # discrete time when resource is first available
param q_follow {Q_PREC};		# the second member of the pairs that form set Q for v_jq
param v_jq {Q_PREC};			# planned interoperation time
param v_disc_jq_ext {Q_PREC};	# discrete planned interoperation time for the MTC route operations between start of machining operation (i=2) of job j
								# and start of machining operation (i=2) of job q (of set Q)
param M;						# large number
param y_disc_solution{JOBS,JOBS,K_RESOURCES};	# the solution to the machining problem is to be fixed as y_2j2qk for the feasibility problem
param z_disc_solution{JOBS,K_RESOURCES};	# the solution to the machining problem is to be fixed as z_2jk for the feasibility problem
#param old_objective;			# In order to compare with the objective from the MTC2-model
param proc_tardi_objective;		# The sum of the total processing times and tardiness (no need for a small weight on t[1,j] since t[2,j] is fixed in the feas model
param p_j_o_postmach_disc{JOBS};	# The sum processing and transport times for the operations no 2--n_j (i.e. machining operation included!!!)
								# Reason: To calculate the job finish time in order to compare with the due dates
param T_length_interval;		# Length (hours) of one interval
param resource_weight{K_RESOURCES};	# weight for the resources in order to avoid symmetries

param proc_time_mach {JOBS};	# processing time for the machining operation
param r_mach {JOBS};			# release dates for the machining problem
param v_mach_jq {Q_PREC};		# planned interoperation time for the MTC route operations between job j and q (of set Q)
param p_postmach{JOBS};			# The sum processing and transport times for the operations no 3--n_j

#---------------------------------------#
# VARIABLES #

var t {I_OP,JOBS} >= 0; 	  	# variable starting time
var x_nail {JOBS,K_mach_RESOURCES,T_ALL_INTERVALS} binary;   # discrete "nail-variable"
var z {I_OP,JOBS,K_RESOURCES} binary;  				# variable machine allocation
var y {I_OP,JOBS,I_OP,JOBS,K_RESOURCES} binary; 	# variable for operation ordering in same resource
var s {JOBS} >= 0;	  	  		# variable completion time
var s_disc {JOBS} >= 0;	  	  	# variable completion time for the discrete machining problem
var h {JOBS} >= 0;	  	  		# variable tardiness
var h_disc {JOBS} >= 0;	  	  	# variable tardiness for the discrete machining problem

var t_mach {JOBS} >= 0; 	  	# variable starting time for the machining problem
var z_mach {JOBS,K_mach_RESOURCES} binary;  		# variable machine allocation for the machining problem
var y_mach {JOBS,JOBS,K_mach_RESOURCES} binary; 	# variable for operation ordering in same resource for the machining problem
var s_mach {JOBS} >= 0;	  	  	# variable completion time for the machining problem
var h_mach {JOBS} >= 0;	  	  	# variable tardiness for the machining problem

#---------------------------------------#
# OBJECTIVES #

# Discrete machining problem objective:
minimize Finish_times_and_tardiness_disc:
sum {j in JOBS} (s_disc[j]+ h_disc[j]);		#minimize job finish times and total tardiness

# Machining problem objective:
minimize Finish_times_and_tardiness_mach:
sum {j in JOBS} (s_mach[j]+ h_mach[j]);	#minimize job finish times and total tardiness

# Feasibility problem objective
minimize Process_times_and_tardiness_feas:
sum {j in JOBS} (s[j]-0.001*t[1,j]+h[j] + sum {i in ACTIVE_I[j], k in K_RESOURCES} resource_weight[k]*z[i,j,k]);

#---------------------------------------#
# CONSTRAINTS FOR THE DISCRETE MACHINING PROBLEM (NAIL VARIABLES)#

# One job is performed once and only once for the discrete machining problem
subject to opconstraints_disc {j in JOBS}:
   sum {k in K_mach_RESOURCES, u in T_ALL_INTERVALS} x_nail[j,k,u] = 1;
   
# Each operation is scheduled to an allowed resource for the machining problem
subject to flexconstraints_disc {j in JOBS, k in K_mach_RESOURCES}:
   sum {u in T_ALL_INTERVALS} x_nail[j,k,u] <= lambda_mach[j,k];
   
# Resource k can only process one job at a time
subject to not_same_time_constr_disc {k in K_mach_RESOURCES, u in 0..T_HORIZON}:   
   sum{j in JOBS, v in max(u-proc_time_disc[j]+1,0)..u}x_nail[j,k,v] <= 1;
   
# Constraints of planned interoperation time for same production order for the machining problem
subject to interop_time_constraints_disc {j_prec in Q_PREC, u in 0..(T_HORIZON-v_disc_jq_ext[j_prec])}:
   sum {k in K_mach_RESOURCES} (sum{u_ext in 0..(u+v_disc_jq_ext[j_prec])}x_nail[q_follow[j_prec],k,u_ext] - sum{u_prec in 0..u}x_nail[j_prec,k,u_prec]) <= 0;
   
# Constraints for the end of the planning horizon, job j can not be scheduled too late, because job q has to be processed before the end of the planning horizon (for jobs (j,q) /in set Q)
subject to end_for_j_prec_constraints {j_prec in Q_PREC, k in K_mach_RESOURCES, u in (T_HORIZON-v_disc_jq_ext[j_prec])..T_HORIZON}:
	x_nail[j_prec,k,u] = 0;
   
#  Fix order of jobs for set P - detta kanske är en bra idé, men tar väldigt mycket minne...
#subject to fix_order_constraints_P {(j_prec_P,q_follow_P) in P_SAME_JOBS, u in T_ALL_INTERVALS}: 
#   sum {k in K_mach_RESOURCES} (x_nail[j_prec_P,k,u] + sum{u_P in 0..u}x_nail[q_follow_P,k,u_P]) <= 1;
  
# Starting constraints for the discrete machining problem
subject to start_constraints1_disc {j in JOBS, k in K_mach_RESOURCES, u in 0..r_disc[j]}:
   x_nail[j,k,u] = 0;

# Starting constraints, resource availability for the discrete machining problem
subject to start_constraints2_disc {j in JOBS, k in K_mach_RESOURCES, u in 0..a_disc[k]}:
   x_nail[j,k,u] = 0;
   
# Define completion time for the discrete machining problem
subject to completion_time_constraints_disc {j in JOBS}:
   sum {k in K_mach_RESOURCES, u in T_ALL_INTERVALS} u*x_nail[j,k,u] + p_j_o_postmach_disc[j] = s_disc[j];
   
# Define tardiness
subject to tardiness_constraints_disc {j in JOBS}:
   h_disc[j] >= s_disc[j]-d_disc[j];

# Ending constraints for the discrete machining problem, job j cannot be started too late, so that it is impossible to complete before the end of the schedule
subject to end_constraints_disc {j in JOBS, k in K_mach_RESOURCES, u in (T_HORIZON - proc_time_disc[j])..T_HORIZON}:
   x_nail[j,k,u] = 0;
   
#---------------------------------------#   

# CONSTRAINTS FOR THE ENGINEER'S MACHINING PROBLEM

# One job is performed once and only once for the machining problem
subject to opconstraints_mach {j in JOBS}:
   sum {k in K_mach_RESOURCES} z_mach[j,k] = 1;
   
# Each operation is scheduled to an allowed resource for the machining problem
subject to flexconstraints_mach {j in JOBS, k in K_mach_RESOURCES}:
   z_mach[j,k] <= lambda_mach[j,k];

# Both y cannot be 1 for two different operations scheduled to the same machine for the machining problem
subject to both_y_not_1_constraints_mach {j in JOBS, q in JOBS, k in K_mach_RESOURCES}:
   y_mach[j,q,k] + y_mach[q,j,k] <= if (j=q) then 2 else z_mach[j,k];

# At least one y must be 1 for two different operations scheduled to the same machine for the machining problem
subject to at_least_one_y_constraints_mach {j in JOBS, q in JOBS, k in K_mach_RESOURCES}:
   y_mach[j,q,k] + y_mach[q,j,k] + 1 >= if (j=q)  then 0 else (z_mach[j,k] + z_mach[q,k]);

# Earliest start when the operation scheduled before has been completed in the same resource for the machining problem
subject to earliest_start_constraints_mach {j in JOBS, q in JOBS, k in K_mach_RESOURCES}:
   t_mach[j] + proc_time_mach[j] - M*(1-y_mach[j,q,k]) <= if (j=q)  then M else t_mach[q];

# Starting constraints for the machining problem
subject to start_constraints1_mach {j in JOBS}:
   t_mach[j] >= r_mach[j];
   
# Starting constraints, resource availability for the machining problem
subject to start_constraints2_mach {j in JOBS, k in K_mach_RESOURCES}:
   t_mach[j] >= a[k]*z_mach[j,k];
   
# Estimates the completion time for the machining problem (p_postmach is the optimal postprocessing time)
subject to completion_time_constraints_mach {j in JOBS}:
   s_mach[j] = t_mach[j] + proc_time_mach[j] + p_postmach[j];
   
# Constraints of planned interoperation time for same production order for the machining problem
subject to interop_time_constraints_mach {j_prec in Q_PREC}:
   s_mach[j_prec] + v_mach_jq[j_prec] <= t_mach[q_follow[j_prec]];
   
# Define tardiness for the machining problem
subject to tardiness_constraints_mach {j in JOBS}:
   h_mach[j] >= s_mach[j]-d[j];
   
# The solution to the machining problem is fixed as y_jqk för the engineer's machining problem
subject to y_fixed_constraints_mach {j in JOBS, q in JOBS, k in K_mach_RESOURCES}:
	y_mach[j,q,k] = y_disc_solution[j,q,k]; 
   
# The solution to the machining problem is fixed as z_jk for the engineer's machining problem
subject to z_fixed_constraints_mach {j in JOBS, k in K_mach_RESOURCES}:
   z_mach[j,k] = z_disc_solution[j,k];
   
   
#---------------------------------------#      
   
# CONSTRAINTS FOR THE FEASIBILITY PROBLEM#
   
# One operation is performed once and only once for the feasibility problem, if zero, the job has not been scheduled
subject to opconstraints_feas {j in JOBS,i in ACTIVE_I[j]}:
   sum {k in K_RESOURCES} z[i,j,k] = 1;

# Each operation is scheduled to an allowed resource
subject to flexconstraints {j in JOBS,i in ACTIVE_I[j], k in K_RESOURCES}:
   z[i,j,k] <= lambda[i,j,k];

# Both y cannot be 1 for two different operations scheduled to the same machine
subject to both_y_not_1_constraints {j in JOBS, q in JOBS, i in ACTIVE_I[j], p in ACTIVE_I[q], k in K_RESOURCES}:
   y[i,j,p,q,k] + y[p,q,i,j,k] <= if (i=p and j=q) then 2 else z[i,j,k];

# At least one y must be 1 for two different operations scheduled to the same machine
subject to at_least_one_y_constraints {j in JOBS, q in JOBS, i in ACTIVE_I[j], p in ACTIVE_I[q], k in K_RESOURCES}:
   y[i,j,p,q,k] + y[p,q,i,j,k] + 1 >= if (i=p and j=q)  then 0 else (z[i,j,k] + z[p,q,k]);
   
# Earliest start when the operation scheduled before has been completed in the same resource
subject to earliest_start_constraints {j in JOBS, q in JOBS, i in ACTIVE_I[j], p in ACTIVE_I[q], k in K_RESOURCES}:
   t[i,j] + proc_time[i,j] - M*(1-y[i,j,p,q,k]) <= if (i=p and j=q)  then M else t[p,q]; 

# Operations in the same job must be scheduled in order and with the time to transport between the resources
subject to same_job_constraints {j in JOBS, i in 1..(n[j]-1)}:
   t[i,j] + proc_time[i,j] + w <= t[i+1,j];
   
# Constraints of planned interoperation time for same production order
subject to interop_time_constraints {j_prec in Q_PREC}:
   s[j_prec] + v_jq[j_prec] <= t[1,q_follow[j_prec]];

# Starting constraints, release dates
subject to start_constraints1 {j in JOBS}:
   t[1,j] >= r[j];

# Starting constraints, resource availability
subject to start_constraints2 {j in JOBS, i in ACTIVE_I[j], k in K_RESOURCES}:
   t[i,j] >= a[k]*z[i,j,k];

# Define completion time
subject to completion_time_constraints {j in JOBS}:
   s[j] = t[n[j],j] + proc_time[n[j],j];

# Define tardiness
subject to tardiness_constraints {j in JOBS}:
   h[j] >= s[j]-d[j];
   
# The solution to the machining problem is fixed as y_2j2qk för the feasibility problem
subject to y_fixed_constraints_feas {j in JOBS, q in JOBS, k in K_RESOURCES}:
	y[2,j,2,q,k] = y_disc_solution[j,q,k]; 
   
# The solution to the machining problem is fixed as z_2jk for the feasibility problem
subject to z2_fixed_constraints_feas {j in JOBS, k in K_RESOURCES}:
   z[2,j,k] = z_disc_solution[j,k];
   
# The solution to the machining problem is fixed as t_2j for the feasibility problem
#subject to t2_fixed_constraints_feas {j in JOBS}:
#   t[2,j] = t_disc_solution[j];

# Sum of completion times and tardiness for the solution of the feasibility problem
#subject to old_objective_constraint:
#  old_objective = sum {j in JOBS} (s[j]+h[j]);


#-------------------------------------------------------------------------#


	 

