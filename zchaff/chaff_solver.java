package zchaff;

import java.util.Vector;

public class chaff_solver {
	
	//** reserver for constants
	database CDatabase;
	Vector<Vector<Integer>> _assignment_stack;
	CSolverStats _stats;
	//** end of reserved space
	
	
	public chaff_solver()
	{
		CDatabase = new database();
		_assignment_stack = new Vector<Vector<Integer>>();
		_stats = new CSolverStats();
	}
	
	public void SAT_SetNumVariables(int numberOfVariables)
	{
		this.set_variable_number(numberOfVariables);
	}
	
	public void set_variable_number(int numberOfVariables)
	{
		_stats.num_free_variables = numberOfVariables;
		_stats.total_num_variables = numberOfVariables;
		while(_assignment_stack.size() <= numberOfVariables)
		{
			_assignment_stack.add(new Vector<Integer>());
		}
	}
	
	
//	int add_orig_clause(Vector<Integer> lits, int n_lits, int gid) {
//		  int cid = add_clause_with_gid(lits, n_lits, gid);
//		  if (cid >= 0) {
//		    clause(cid).set_status(CLAUSE_STATUS.ORIGINAL_CL);
//		    clause(cid)._activity = 0;
//		  }
//		  return cid;
//		}
//	int SAT_AddClause(clause_lits, clause_lits.size() ,groupid)
//	{
//		
//	}

}


class CSolverStats
{
	int num_free_variables = 0;
	int total_num_variables = 0;
}

class CLAUSE_STATUS {
    static int ORIGINAL_CL=0;
    static int CONFLICT_CL=1;
    static int DELETED_CL=2;
}