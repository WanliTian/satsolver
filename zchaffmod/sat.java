package zchaffmod;

import java.io.BufferedReader;
import java.io.DataInputStream;
import java.io.FileInputStream;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.Date;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Vector;



public class sat {

	/**
	 * @param args
	 */
	int NO_VALUE = -1;
    int NO_MORE_MOVES = -1;
    int CONFLICT_DETECTED = -2;
    int CHANGE = 1;
    int NO_CHANGE = 0;
    int MAX_WEIGHT = 0;
    int SATISFIABLE = 1;
    int UNSATISFIABLE = 2;
    int UNSATISFIABLEuA = 3;
    
    int VariableNotInClause = 0; 
    int VariableInClause = 1;
    int VariableNegationInClause = 2;
    
    int _numberOfVariables = 0 , _numberOfClauses = 0;
    int domain[] = {1,0};
    int assignments[] ;
    CSP csp;
    
    Variable variables[];
    CSatSolver _stats;
    CSolverParameters _params;
    Vector<Pair> _ordered_vars;
    
    int _dlevel = 0; // decision level
    
    Vector<Vector<Integer>> _assignmentStack;
    
    HashMap<String, Integer> collision;
    int top_unsat_cls ;
    
    HashMap<Integer, Integer> _shrinking_cls;
    
    public sat(String filename)
    {
	    System.out.println("ZCHAFF");
	    csp = generateConstraints(filename);
	    initialize();
	    
	    
	    boolean result = false;
    	result = (dpll(csp.constraints)==SATISFIABLE);
	    if(result){
	        System.out.println("s Satisfiable");
	        int value = 0;
	        System.out.print("v");
	        for(int index = 0 ; index < _numberOfVariables ; index++ )
	        {
	            value = index+1;
	            value *= (assignments[index]==1)? 1 : -1;
	            System.out.print(" "+value);
	        }
	        System.out.print(" 0");
	        System.out.println();
	    }
	    else {
	        System.out.println("Unsatisfiable");
	    }
	}
    
    public void initialize()
    {
    	assignments = new int[_numberOfVariables+1];
    	_assignmentStack = new Vector<Vector<Integer>>();
    	
    	while(_assignmentStack.size() <= _numberOfVariables)
    	{
    		_assignmentStack.add(new Vector<Integer>());
    	}
    	
    	_stats = new CSatSolver();
    	_stats.outcome = _stats.UNDETERMINED;
    	
    	_params = new CSolverParameters();
    	init_parameters();
    	
    	_shrinking_cls = new HashMap<Integer,Integer>();
    	
    }
    
    void init_parameters() {
	  _params.verbosity                           = 0;
	  _params.time_limit                          = 3600 * 24;  // a day
	  _params.shrinking.size                      = 95;
	  _params.shrinking.enable                    = true;
	  _params.shrinking.upper_bound               = 800;
	  _params.shrinking.lower_bound               = 600;
	  _params.shrinking.upper_delta               = -5;
	  _params.shrinking.lower_delta               = 10;
	  _params.shrinking.window_width              = 20;
	  _params.shrinking.bound_update_frequency    = 20;

	  _params.decision.base_randomness            = 0;
	  _params.decision.decay_period               = 40;
	  _params.decision.bubble_init_step           = 0x400;

	  _params.cls_deletion.enable                 = true ;
	  _params.cls_deletion.head_activity          = 500;
	  _params.cls_deletion.tail_activity          = 10;
	  _params.cls_deletion.head_num_lits          = 6;
	  _params.cls_deletion.tail_num_lits          = 45;
	  _params.cls_deletion.tail_vs_head           = 16;
	  _params.cls_deletion.interval               = 600;

	  _params.restart.enable                      = true;
	  _params.restart.interval                    = 700;
	  _params.restart.first_restart               = 7000;
	  _params.restart.backtrack_incr              = 700;
    	}
    
    public int solve()
    {
    	if(_stats.outcome==_stats.UNDETERMINED)
    	{
    		init_solve();
    		
    		if(preprocess() == _stats.CONFLICT)
    		{
    			_stats.outcome = _stats.UNSATISFIABLE;
    		}
    		else
    		{
    			real_solve();
    		}
    	}
    	
    	return _stats.outcome;
    }
    
    public void init_solve()
    {
    	_stats.init_stats();
    	_stats.re_init_stats(_params);
    	
    	_stats.been_reset = false;
    	
    	for(int index = 1 ; index <= _numberOfVariables ; index++)
    	{
    		variables[index]._scores[0] = variables[index]._lits_count[0];
    		variables[index]._scores[1] = variables[index]._lits_count[1];
    	}
    	
    	_ordered_vars = new Vector<Pair>(_numberOfVariables);
    	update_var_score();
    	
    	// set random seed
    	top_unsat_cls = csp.constraints.size();
    	top_unsat_cls--;
    	
    	_stats.shrinking_benefit = 0;
    	_shrinking_cls.clear();
    	_stats.shrinking_cls_length = 0;
    	
    }
    
    
    public int preprocess()
    {
    	return _stats.UNDETERMINED;
    }
    
    public void real_solve()
    {
    	while(_stats.outcome == _stats.UNDETERMINED)
    	{
    		run_periodic_functions();
    		
    		if(decide_next_branch())
    		{
    			while(deduce()==_stats.CONFLICT)
        		{
        			int blevel;
        			blevel = analyze_conflicts();
        			if(blevel < 0)
        			{
        				_stats.outcome = _stats.UNSATISFIABLE;
        				return;
        			}
        		}//end while deduce
    		}//end if
    		else
    		{
    			_stats.outcome = _stats.NO_NEXT_BRANCH;
    			return;
    		}//end else
    		
    	}
    }
    
    public void run_periodic_functions()
    {
    	
    }
    
    public boolean decide_next_branch()
    {
    	return false;
    }
    
    
    public int deduce()
    {
    	
    	return _stats.CONFLICT;
    }
    
    public int analyze_conflicts()
    {
    	
    	return 0;
    }
    
    
    public void update_var_score()
    {
    	
    }
    
    
    
	public boolean CheckResult(int assignment[],int conflicts[])
    {
        int global_status = 1;
        for (Clause constraint : csp.constraints) {
            global_status&=checkClauseResult(constraint, assignment,conflicts);
        }
     return (global_status==1)?true:false;   
    }
    
    /**
     *
     * @param constraint
     * @param assignment
     * @param conflicts
     * @return
     */
    public int checkClauseResult(Clause constraint , int assignment[],int conflicts[])
    {
        int val = 0;
        Vector possibleConflicts = new Vector(constraint.variable.size());        
        for(int cspvar:constraint.variable)
        {
            int key = abs(cspvar);
            int value = assignment[key-1];
            value = (cspvar<0)?(value+1)%2:value;
            val|=value;
        }
        if(val==0)
        {
            for (Iterator it = possibleConflicts.iterator(); it.hasNext();) {
                int key = (Integer)it.next();
                conflicts[key-1]+=1;     
            }
        }
        return val;
        
    }
    
    
    public int dpll(ArrayList<Clause> source)
    {
    	
    	return 0;
    	
    }
    
    public void assignVariable(Variable variable)
    {
    	assignments[abs(variable.key)-1]=(variable.key>0?1:0);
    }
    
    public ArrayList<Integer> getVariablesInClause(Clause clause)
    {
    	ArrayList<Integer> vars = new ArrayList<Integer>();
    	for (int variable : clause.variable) {
			vars.add(variable);
		}
    	return vars;
    }
    public ArrayList<Clause> reduce(ArrayList<Clause> source,Variable variable)
    {
    	int clause_index = 0 ;
    	ArrayList<Clause> local = copy(source);
    	assignVariable(variable);
    	for (Clause clause : source) {
			if((clauseContainsVariable(clause,variable)==VariableInClause))
			{
				local.remove(clause);
			}else if((clauseContainsVariable(clause,variable)==VariableNegationInClause))
			{
				clause = removeVariableFromClause(clause,variable);
				local.set(clause_index, clause);
				clause_index++;
			}else
			{
				//VariableNotInClause
				clause_index++;
			}
			
		}
    	return local;
    }
    
    
    public int clauseContainsVariable(Clause clause,Variable variable)
    {
    	int key = variable.key;
    	int value = abs(key);
    	for (int i = 0; i < clause.variable.size(); i++) {
			int var = clause.variable.get(i);
			if(var==variable.key) return VariableInClause;
			else if(var==-variable.key) return VariableNegationInClause;
		}
    	return VariableNotInClause;
    	
    }
    
    public Clause removeVariableFromClause(Clause source,Variable variable)
    {
    	for (int i = 0; i < source.variable.size(); i++) {
			int var = source.variable.get(i);
			if(abs(var)==(abs(variable.key)))
			{
				source.variable.remove(i);
				break;
			}
		}
    	return source;
    }
    public ArrayList<Clause> copy(ArrayList<Clause> source)
    {
    	ArrayList<Clause> local = new ArrayList<Clause>(source.size());
    	for (Iterator iterator = source.iterator(); iterator.hasNext();) {
			Clause clause = (Clause) iterator.next();
			local.add(clause);
		}
    	return local;
    }
    
    public int abs(int value)
    {
        return (value>=0)?value:-value;
    }
    
    public CSP generateConstraints(String filename)
    {
        Vector<String> clauses = parseFile(filename);
        return generateClauses(clauses);
    }
    
    public CSP generateClauses(Vector<String> clauses)
    {
        CSP csp = new CSP();
        csp.constraints = new ArrayList<Clause>(_numberOfClauses);
        int clause_index = 0;
        for (Iterator<String> it = clauses.iterator(); it.hasNext();) {
            String string = it.next();
            String split[] = string.split(" ");
            Clause clause = new Clause();
            clause.variable = new ArrayList<Integer>(split.length-1); // last 0 is not counted
            int variable_index = 0 ;
            for (String string1 : split) {
                int value = Integer.parseInt(string1);
                if(value==0) break;
                
                Variable var = variables[abs(value)];
                int sign = sign(value);
                var._lits_count[sign]++;
                if(split.length-1==2) var._2_lits_count[sign]++;
                var.clauses[sign].add(csp.constraints.size());
                
                clause.variable.add(value);
                variable_index++;
            }
           csp.constraints.add(clause);
           clause_index++;
        }
        return csp;
    }
    
    public int sign(int value)
    {
    	return value>0?1:0;
    }
    
    public Vector<String> parseFile(String filename)
    {
        try
        {
            FileInputStream filestream = new FileInputStream(filename);
            DataInputStream in = new DataInputStream(filestream);
            BufferedReader br = new BufferedReader(new InputStreamReader(in));
            String line;
            int lineNumber=0,clauseIndex=0;
            Vector<String> clauses = new Vector<String>();
            while((line=br.readLine())!=null)
            {
            	line=line.trim();
            	if(line.equals("")) continue;
                lineNumber++;
                switch(lineNumber)
                {
                    case 1:
                        //Nothing much to do .Its just a comment line in .cnf file
                    break;
                    case 2:
                        String temp[] = line.split(" ");
                        _numberOfVariables = Integer.parseInt(temp[2]);
                        _numberOfClauses = Integer.parseInt(temp[3]);
                        variables = new Variable[_numberOfVariables+1];
                        for (int i = 1; i <= _numberOfVariables; i++) {
                        	variables[i] = new Variable();
						}
                        break;
                    default:
                        clauses.add(line);
                        clauseIndex++;
                    break;
                }
            }
            return clauses;
            
        }catch(Exception e)
        {
            System.out.println(e.getMessage());
            return null;
        }
    }
    
    public static void printTime()
    {
    	Date date = new Date();
        
        // display time and date using toString()
        System.out.println(date.toString());
    }
    
	public static void main(String[] args) {

	}

}

class Variable
{
    int key;
    
    Vector<Integer> clauses[] = new Vector[2];
    int _lits_count[] = new int[2];
    
    int _2_lits_count[] = new int[2];
    
    int _scores[] = new int[2];
    
    public Variable()
    {
    	clauses[0] = new Vector<Integer>();
    	clauses[1] = new Vector<Integer>();
    	
    }
}

class CSP
{
    ArrayList<Clause> constraints;
    boolean global_status = false;
}

class Clause
{
    ArrayList<Integer> variable;
    boolean local_status = false;
    int VarIndex[] = new int[2];
}

class CSatSolver
{
	int UNDETERMINED = 0;
	int CONFLICT = 1;
	int UNSATISFIABLE = 2;
	int SATISFIABLE = 3;
	int NO_NEXT_BRANCH = 4;
	
	int outcome = 0;
	
	int init_num_clauses         = num_clauses();
	int init_num_literals        = num_literals();
	int num_deleted_clauses      = 0;
	int num_del_orig_cls         = 0;
	int num_deleted_literals     = 0;
	int num_enlarge              = 0;
	int num_compact              = 0;
	
	int _numLiterals = 0;
	int _numClauses = 0;
	
	int next_restart         = 0;
	int restart_incr         = 0;
	int next_cls_deletion    = 0;
	int next_var_score_decay = 0;
	int current_randomness   = 0;
	
	int total_bubble_move            = 0;
	int num_decisions                = 0;
	int num_decisions_stack_conf     = 0;
	int num_decisions_vsids          = 0;
	int num_decisions_shrinking      = 0;
	int num_backtracks               = 0;
	int max_dlevel                   = 0;
	int num_implications             = 0;
	int num_restarts                 = 0;
	int num_shrinkings               = 0;
	int finish_cpu_time              = 0;
	int random_seed                  = 0;
	boolean been_reset = false;
	
	int shrinking_benefit = 0;
	int shrinking_cls_length = 0;
	
	public void init_stats()
	{
		init_num_clauses         = num_clauses();
		init_num_literals        = num_literals();
		num_deleted_clauses      = 0;
		num_del_orig_cls         = 0;
		num_deleted_literals     = 0;
		num_enlarge              = 0;
		num_compact              = 0;
		
		 _numLiterals = 0;
		 _numClauses = 0;
	}
	
	public void re_init_stats(CSolverParameters _params)
	{
	  this.outcome              = UNDETERMINED;
	  this.next_restart         = _params.restart.first_restart;
	  this.restart_incr         = _params.restart.backtrack_incr;
	  this.next_cls_deletion    = _params.cls_deletion.interval;
	  this.next_var_score_decay = _params.decision.decay_period;
	  this.current_randomness   = _params.decision.base_randomness;

	  this.total_bubble_move            = 0;
	  this.num_decisions                = 0;
	  this.num_decisions_stack_conf     = 0;
	  this.num_decisions_vsids          = 0;
	  this.num_decisions_shrinking      = 0;
	  this.num_backtracks               = 0;
	  this.max_dlevel                   = 0;
	  this.num_implications             = 0;
	  this.num_restarts                 = 0;
	  this.num_del_orig_cls             = 0;
	  this.num_shrinkings               = 0;
	  this.finish_cpu_time              = 0;
	  this.random_seed                  = 0;
	}
    
    int num_clauses()
    {
    	return _numClauses;
    }
    
    int num_literals()
    {
    	return _numLiterals;
    }
    		
}

class CSolverParameters {
	  float         time_limit;
	  int           verbosity;

	  class shrinking{
	    int    size;
	    boolean enable;
	    int         upper_bound;
	    int         lower_bound;
	    int         upper_delta;
	    int         lower_delta;
	    int         bound_update_frequency;
	    int    window_width;
	  }
	  shrinking shrinking = new shrinking();

	  class decision {
	    int         base_randomness;
	    int         bubble_init_step;
	    int         decay_period;
	  } 
	  decision decision = new decision();

	  class cls_deletion{
	    boolean        enable;
	    int    interval;
	    int    head_activity;
	    int    tail_activity;
	    int    head_num_lits;
	    int    tail_num_lits;
	    int         tail_vs_head;
	  } 
	  cls_deletion cls_deletion = new cls_deletion(); 

	  class restart {
	    boolean        enable;
	    int         interval;
	    int         first_restart;
	    int         backtrack_incr;
	  } 
	  
	  restart restart = new restart();
	  
	}

class CImplication {
	  int lit;
	  int antecedent;
	}

class Pair
{
	Variable var;
	int score;
	int value;
}