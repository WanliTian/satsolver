package zchaffmod;

import java.io.BufferedReader;
import java.io.DataInputStream;
import java.io.FileInputStream;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Date;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Queue;
import java.util.Vector;
import java.util.prefs.BackingStoreException;

import javax.net.ssl.SSLEngineResult.Status;

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
    Pair _ordered_vars[];
    
    int _dlevel = 0; // decision level
    int _max_score_pos ;
    int _implication_id;
    Vector<Integer> _conflicts;  
    Vector<Vector<Integer>> _assignmentStack;
    
    HashMap<String, Integer> collision;
    int top_unsat_cls ;
    ImplicationQueue _implication_queue;
    
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
    	_implication_queue = new ImplicationQueue();
    	
    	_conflicts = new Vector<Integer>();
    	
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
    	
    	_ordered_vars = new Pair[_numberOfVariables];
    	for (int i = 0; i < _numberOfVariables; i++) {
			_ordered_vars[i] = new Pair();
		}
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
    	
    	//1. detect unused variables
    	Vector<Integer> un_used = new Vector<Integer>();
    	for(int index=1,sz =variables.length;index<sz;index++)
    	{
    		Variable v = variables[index];
    		if(v._lits_count[0]==0 && v._lits_count[1]==0)
    		{
    			un_used.add(index);
    		}
    		queue_implication(index+1, Variable.NULL_CLAUSE);
    		// int r = deduce()
    	}
    	
    	//2. pure literals
    	Vector<Integer> uni_phased = new Vector<Integer>();
		for (int i = 1, sz = variables.length; i < sz; ++i) {
		  Variable  v = variables[i];
		if (v._value != Variable.UNKNOWN)
		    continue;
		if (v._lits_count[0] == 0) {  // no positive phased lits.
			queue_implication(i+i+1, Variable.NULL_CLAUSE);
			uni_phased.add(-i);
		}
		else if (v._lits_count[1] == 0) {  // no negative phased lits.
			queue_implication(i+i, Variable.NULL_CLAUSE);
			uni_phased.add(i);
		  }
		}
    	//3. unit clauses
		 for (int i = 0, sz = csp.constraints.size(); i < sz; ++i) {
			 ArrayList<Clause> clauses = csp.constraints;
		    if (clauses.get(i)._status != CLAUSE_STATUS.DELETED_CL &&
		        clauses.get(i)._num_lits == 1 &&
		        variables[clauses.get(i).literals.get(0).var_index()]._value == Variable.UNKNOWN)
		      queue_implication(clauses.get(i).literals.get(0).s_var(), i);
		  }
		 
		 if(deduce()==_stats.CONFLICT)
		 {
			 return _stats.CONFLICT;
		 }
    	return _stats.NO_CONFLICT;
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
    	// a. restart
    	if(_params.restart.enable && _stats.num_backtracks > _stats.next_restart &&
    			_shrinking_cls.size()==0)
    	{
    		_stats.next_restart = _stats.num_backtracks + _stats.restart_incr;
    		delete_unrelevant_clauses();
    		restart();
    		
    		if(_stats.num_restarts%5 == 1)
    		{
    			compact_lit_pool();
    		}
    	}
    	
    	// b. decay variable score
    	if (_stats.num_backtracks > _stats.next_var_score_decay) {
    	    _stats.next_var_score_decay = _stats.num_backtracks +
    	                                  _params.decision.decay_period;
    	    decay_variable_score();
    	  }
    }
    
    public void compact_lit_pool()
    {
    	
    }
    
    public void delete_unrelevant_clauses()
    {
    	
    }
    
    public void restart()
    {
    	
    }
    
    public void decay_variable_score()
    {
    	
    }
    
    public boolean decide_next_branch()
    {
    	  if (_dlevel > 0)
    		    
    		  if (!(_implication_queue._queue.size()==0)) {
    		    // some hook function did a decision, so skip my own decision making.
    		    // if the front of implication queue is 0, that means it's finished
    		    // because var index start from 1, so 2 *vid + sign won't be 0.
    		    // else it's a valid decision.
    		    return (_implication_queue._queue.poll().lit != 0);
    		  }
    		  int s_var = 0;
    		  if (_params.shrinking.enable) {
    		    while (!(_shrinking_cls.size()==0)) {
//    		      s_var = _shrinking_cls.values().iterator().next().second;
//    		      _shrinking_cls.erase(_shrinking_cls.begin());
    		      if (variables[s_var >> 1]._value == Variable.UNKNOWN) {
    		        _stats.num_decisions++;
    		        _stats.num_decisions_shrinking++;
    		        ++_dlevel;
    		        queue_implication(s_var ^ 0x1, Variable.NULL_CLAUSE);
    		        return true;
    		      }
    		    }
    		  }

     		  if (!(_implication_queue._queue.size()==0))
    		     return (_implication_queue._queue.poll().lit != 0);

    		  ++_stats.num_decisions;
    		  if (_stats.num_free_variables == 0)  // no more free vars
    		     return false;

    		  boolean cls_sat = true;
    		  int i, sz, var_idx, score, max_score = -1;

    		  for (; csp.constraints.get(top_unsat_cls)._status != CLAUSE_STATUS.ORIGINAL_CL; --top_unsat_cls) {
    		    Clause cl=csp.constraints.get(top_unsat_cls);
    		    if (cl._status != CLAUSE_STATUS.CONFLICT_CL)
    		      continue;
    		    cls_sat = false;
    		    if (cl._sat_lit_idx < (int)cl._num_lits &&
    		        literal_value(cl.literals.get(cl._sat_lit_idx)) == 1)
    		      cls_sat = true;
    		    if (!cls_sat) {
    		      max_score = -1;
    		      for (i = 0, sz = cl._num_lits; i < sz; ++i) {
    		        var_idx = cl.literals.get(i).var_index();
    		        if (literal_value(cl.literals.get(i)) == 1) {
    		          cls_sat = true;
    		          cl._sat_lit_idx = i;
    		          break;
    		        }
    		        else if (variables[var_idx]._value == Variable.UNKNOWN) {
    		          score = variables[var_idx].score();
    		          if (score > max_score) {
    		            max_score = score;
    		            s_var = var_idx * 2;
    		          }
    		        }
    		      }
    		    }
    		    if (!cls_sat)
    		      break;
    		  }
    		  if (!cls_sat && max_score != -1) {
    		    ++_dlevel;
    		    if (_dlevel > _stats.max_dlevel)
    		      _stats.max_dlevel = _dlevel;
    		    Variable v = variables[s_var >> 1];
    		    if (v._scores[0] < v._scores[1])
    		      s_var += 1;
    		    else if (v._scores[0] == v._scores[1]) {
    		      if (v._2_lits_count[0] > v._2_lits_count[1])
    		        s_var+=1;
    		      else if (v._2_lits_count[0] == v._2_lits_count[1])
    		        s_var+=Math.random()%2;
    		    }
//    		    assert(s_var >= 2);
    		    queue_implication(s_var, Variable.NULL_CLAUSE);
    		    ++_stats.num_decisions_stack_conf;
    		    return true;
    		  }

    		  for (int i1 = _max_score_pos; i1 < _ordered_vars.length; ++i1) {
    		    Variable  var = variables[_ordered_vars[i1].first];
    		    if (var._value == Variable.UNKNOWN && var.enable_branch) {
    		      // move th max score position pointer
    		      _max_score_pos = i1;
    		      // make some randomness happen
    		      if (--_stats.current_randomness < _params.decision.base_randomness)
    		        _stats.current_randomness = _params.decision.base_randomness;
    		      int randomness = _stats.current_randomness;
    		      if (randomness >= _stats.num_free_variables)
    		        randomness = _stats.num_free_variables - 1;
    		      int skip = (int)(Math.random()*(1 + randomness));
    		      int index = i1;
    		      while (skip > 0) {
    		        ++index;
    		      if (variables[_ordered_vars[index].first]._value == Variable.UNKNOWN &&
    		    		  variables[_ordered_vars[index].first].enable_branch)
    		        --skip;
    		      }
    		      Variable  ptr = variables[_ordered_vars[index].first];
//    		      assert(ptr.value() == Variable.UNKNOWN && ptr.is_branchable());
    		      int sign = 0;
    		      if (ptr._scores[0] < ptr._scores[1])
    		        sign += 1;
    		      else if (ptr._scores[0] == ptr._scores[1]) {
    		        if (ptr._2_lits_count[0] > ptr._2_lits_count[1])
    		          sign += 1;
    		        else if (ptr._2_lits_count[0] == ptr._2_lits_count[1])
    		          sign += (int)(Math.random()*2);
    		      }
    		      int var_idx2 =_ordered_vars[index].first; //ptr - &(*variables().begin());
    		      s_var = var_idx2 + var_idx2 + sign;
    		      break;
    		    }
    		  }
//    		  assert(s_var >= 2);  // there must be a free var somewhere
    		  ++_dlevel;
    		  if (_dlevel > _stats.max_dlevel)
    		    _stats.max_dlevel = _dlevel;
    		  ++_stats.num_decisions_vsids;
    		  _implication_id = 0;
    		  queue_implication(s_var, Variable.NULL_CLAUSE);
    		  return true;
    }
    
    int literal_value(CLitPoolElement l) {
        // note: it will return 0 or 1 or other, here "other" may not equal UNKNOWN
          return (variables[l.var_index()]._value ^ l.var_sign());
        }
    
    
    public int deduce()
    {
    	 while (!(_implication_queue._queue.size()==0)) {
		    CImplication imp = _implication_queue._queue.poll();
		    int lit = imp.lit;
		    int vid = lit>>1;
		    int cl = imp.antecedent;
//		    _implication_queue.pop();
		    Variable  var = variables[vid];
		    if (var._value == Variable.UNKNOWN) {  // an implication
		      set_var_value(vid, ((lit & 0x1)==0?1:0), cl, _dlevel);
		    }
		    else if (var._value == (int)(lit & 0x1)) {
		      // a conflict
		      // note: literal & 0x1 == 1 means the literal is in negative phase
		      // when a conflict occure at not current dlevel, we need to backtrack
		      // to resolve the problem.
		      // conflict analysis will only work if the conflict occure at
		      // the top level (current dlevel)
		      _conflicts.add(cl);
		      break;
		    } else {
		      // so the variable have been assigned before
		      // update its antecedent with a shorter one
		      if (var._antecedent != Variable.NULL_CLAUSE &&
		          csp.constraints.get(cl)._num_lits < csp.constraints.get(var._antecedent)._num_lits)
		        var._antecedent = cl;
		      assert(var._dlevel <= _dlevel);
		    }
		  }
		  // if loop exited because of a conflict, we need to clean implication queue
		  while (!(_implication_queue._queue.size()==0))
		    _implication_queue._queue.poll();
		  return ((_conflicts.size()>0) ? _stats.CONFLICT : _stats.NO_CONFLICT);
    }
    
    public void set_var_value(int v, int value, int ante, int dl) {
//        assert(value == 0 || value == 1);
        Variable var = variables[v];
        assert(var._value == Variable.UNKNOWN);
        assert(dl == _dlevel);

        var._dlevel=dl;
        var._value=value;
        var._antecedent = ante;
        var._assign_stack_pos = _assignmentStack.get(dl).size();
        _assignmentStack.get(dl).add(v * 2 + (value==0?1:0));
        set_var_value_BCP(v, value);

        ++_stats.num_implications ;
        if (var.enable_branch)
            --_stats.num_free_variables;
    }
    
    public void set_var_value_BCP(int v, int value) {
//    	  Vector<CLitPoolElement> watchs = variables[v].clauses[value];
//    	  for (Iterator itr = watchs.begin();
//    	       itr != watchs.end(); ++itr) {
//    	    int cl_idx;
//    	    CLitPoolElement  other_watched = itr;
//    	    CLitPoolElement  watched = itr;
//    	    int dir = watched.direction();
//    	    CLitPoolElement ptr = watched;
//    	    while (true) {
//    	      ptr += dir;
//    	      if (ptr->val() <= 0) {  // reached one end of the clause
//    	        if (dir == 1)  // reached the right end, i.e. spacing element is cl_id
//    	          cl_idx = ptr->get_clause_index();
//    	        if (dir == watched->direction()) {  // we haven't go both directions.
//    	          ptr = watched;
//    	          dir = -dir;                     // change direction, go the other way
//    	          continue;
//    	        }
//    	        // otherwise, we have already go through the whole clause
//    	        int the_value = literal_value(*other_watched);
//    	        if (the_value == 0)  // a conflict
//    	          _conflicts.push_back(cl_idx);
//    	        else if (the_value != 1)  // i.e. unknown
//    	          queue_implication(other_watched->s_var(), cl_idx);
//    	        break;
//    	      }
//    	      if (ptr->is_watched()) {  // literal is the other watched lit, skip it.
//    	        other_watched = ptr;
//    	        continue;
//    	      }
//    	      if (literal_value(*ptr) == 0)  // literal value is 0, keep going
//    	        continue;
//    	      // now the literal's value is either 1 or unknown, watch it instead
//    	      int v1 = ptr->var_index();
//    	      int sign = ptr->var_sign();
//    	      variable(v1).watched(sign).push_back(ptr);
//    	      ptr->set_watch(dir);
//    	      // remove the original watched literal from watched list
//    	      watched->unwatch();
//    	      *itr = watchs.back();  // copy the last element in it's place
//    	      watchs.pop_back();     // remove the last element
//    	      --itr;                 // do this so with don't skip one during traversal
//    	      break;
//    	    }
    	  }
    
    public int analyze_conflicts()
    {
    	if (_dlevel == 0) {
    		
    		_conflicts.clear();
    		back_track(0);
    		return -1;
    	}
    	return  conflict_analysis_firstUIP();
    		
    }
    
    boolean _mark_increase_score;
    public int conflict_analysis_firstUIP() {
    	  int min_conf_id = _conflicts.get(0);
    	  int min_conf_length = -1;
    	  int gflag;
    	  _mark_increase_score = false;
    	  if (_conflicts.size() > 1) {
    	    for (int index=0;index<_conflicts.size;index++) {
//    	      assert(_num_in_new_cl == 0);
//    	      assert(dlevel() > 0);
    	      Clause cl = csp.constraints.get(_conflicts.get(index));
    	      mark_vars(cl, -1);
    	      // current dl must be the conflict cl.
    	      vector <int> & assignments = *_assignment_stack[dlevel()];
    	      // now add conflict lits, and unassign vars
    	      for (int i = assignments.size() - 1; i >= 0; --i) {
    	        int assigned = assignments[i];
    	        if (variable(assigned >> 1).is_marked()) {
    	          // this variable is involved in the conflict clause or its antecedent
    	          variable(assigned>>1).clear_marked();
    	          --_num_marked;
    	          int ante_cl = variable(assigned>>1).get_antecedent();
    	          if ( _num_marked == 0 ) {
    	            // the first UIP encountered, conclude add clause
    	            assert(variable(assigned>>1).new_cl_phase() == UNKNOWN);
    	            // add this assignment's reverse, e.g. UIP
    	            _conflict_lits.add(assigned ^ 0x1);
    	            ++_num_in_new_cl;
    	            variable(assigned>>1).set_new_cl_phase((assigned^0x1)&0x1);
    	            break;
    	          } else {
    	            assert(ante_cl != Variable.NULL_CLAUSE);
    	            mark_vars(ante_cl, assigned >> 1);
    	          }
    	        }
    	      }
    	      if (min_conf_length == -1 ||
    	          (int)_conflict_lits.size() < min_conf_length) {
    	        min_conf_length = _conflict_lits.size();
    	        min_conf_id = cl;
    	      }

    	      for (vector<int>::iterator vi = _conflict_lits.begin(); vi !=
    	           _conflict_lits.end(); ++vi) {
    	        int s_var = *vi;
    	        CVariable & var = variable(s_var >> 1);
    	        assert(var.new_cl_phase() == (unsigned)(s_var & 0x1));
    	        var.set_new_cl_phase(UNKNOWN);
    	      }
    	      _num_in_new_cl = 0;
    	      _conflict_lits.clear();
    	      _resolvents.clear();
    	    }
    	  }

    	  assert(_num_marked == 0);
    	  cl = min_conf_id;
    	  clause(cl).activity() += 5;
    	  _mark_increase_score = true;
    	  mark_vars(cl, -1);
    	  gflag = clause(cl).gflag();
    	  vector<Integer>  assignments = _assignmentStack[dlevel()];
    	  for (int i = assignments.size() - 1; i >= 0; --i) {
    	    int assigned = assignments[i];
    	    if (variable(assigned >> 1).is_marked()) {
    	      variable(assigned>>1).clear_marked();
    	      --_num_marked;
    	      ClauseIdx ante_cl = variable(assigned>>1).get_antecedent();
    	      if ( _num_marked == 0 ) {
    	        _conflict_lits.add(assigned ^ 0x1);
    	        ++_num_in_new_cl;
    	        variable(assigned >> 1).set_new_cl_phase((assigned ^ 0x1) & 0x1);
    	        break;
    	      } else {
    	        gflag |= clause(ante_cl).gflag();
    	        mark_vars(ante_cl, assigned >> 1);
    	        clause(ante_cl).activity() += 5;
    	      }
    	    }
    	  }
    	  return finish_add_conf_clause(gflag);
    }
    public void back_track(int blevel) {
	  for (int i = dlevel(); i >= blevel; --i) {
	    Vector<Integer>  assignments = _assignmentStack.get(i);
	    for (int j = assignments.size() - 1 ; j >= 0; --j)
	      unset_var_value(assignments.get(j)>>1);
	    assignments.clear();
	  }
	  _dlevel = blevel - 1;
	  if (dlevel() < 0 )
	    _dlevel = 0;
	  ++_stats.num_backtracks;
    	}
    
    public void unset_var_value(int v) {
	  if (v == 0)
		    return;
		  Variable var = variables[v];
		  var._value=Variable.UNKNOWN;
		  var._antecedent=Variable.NULL_CLAUSE;
		  var._dlevel=-1;
		  var._assign_stack_pos = -1;

		  if (var.enable_branch) {
		    ++_stats.num_free_variables;
		    if (var._var_score_pos < _max_score_pos){
		      _max_score_pos = var._var_score_pos;
		      }
		    else
		    {
		    	
		    }
		  }
    }
    public int dlevel()
    {
    	return _dlevel;
    }
    
    public void queue_implication(int lit, int ante_clause) {
        CImplication i = new CImplication();
        i.lit = lit;
        i.antecedent = ante_clause;
        _implication_queue._queue.add(i);
      }
    
    public void update_var_score()
    {
    	for (int i = 1, sz = _numberOfVariables; i < sz; ++i) {
    	    _ordered_vars[i-1].first = i;
    	    _ordered_vars[i-1].second = variables[i].score();
    	  }
//    	  ::stable_sort(_ordered_vars.begin(), _ordered_vars.end(), cmp_var_stat);
    	Arrays.sort(_ordered_vars);
    	  for (int i = 0, sz =  _ordered_vars.length; i < sz; ++i)
    	    variables[_ordered_vars[i].first]._var_score_pos=i;
    	  _max_score_pos = 0;
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
        Vector possibleConflicts = new Vector(constraint.literals.size());        
        for(CLitPoolElement cspvar:constraint.literals)
        {
            int key = abs(cspvar._val);
            int value = assignment[key-1];
            value = (cspvar._val<0)?(value+1)%2:value;
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
    
    public ArrayList<CLitPoolElement> getVariablesInClause(Clause clause)
    {
    	ArrayList<CLitPoolElement> vars = new ArrayList<CLitPoolElement>();
    	for (CLitPoolElement variable : clause.literals) {
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
    	for (int i = 0; i < clause.literals.size(); i++) {
			int var = clause.literals.get(i)._val;
			if(var==variable.key) return VariableInClause;
			else if(var==-variable.key) return VariableNegationInClause;
		}
    	return VariableNotInClause;
    	
    }
    
    public Clause removeVariableFromClause(Clause source,Variable variable)
    {
    	for (int i = 0; i < source.literals.size(); i++) {
			int var = source.literals.get(i)._val;
			if(abs(var)==(abs(variable.key)))
			{
				source.literals.remove(i);
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
            clause.literals = new ArrayList<CLitPoolElement>(split.length-1); // last 0 is not counted
            int variable_index = 0 ;
            for (String string1 : split) {
                int value = Integer.parseInt(string1);
                if(value==0) break;
                
                Variable var = variables[abs(value)];
                int sign = sign(value);
                var._lits_count[sign]++;
                if(split.length-1==2) var._2_lits_count[sign]++;
                var.clauses[sign].add(csp.constraints.size());
                CLitPoolElement element = new CLitPoolElement();
                element.set(abs(value), (value<0)?1:0);
                clause.literals.add(element);
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
	static int UNKNOWN = -1;
	static int NULL_CLAUSE = -1;
	
    int key;
    int _dlevel;
    int _var_score_pos;
    int _assign_stack_pos;
    boolean enable_branch;
    boolean _marked;
    int _value = UNKNOWN;
    int _antecedent ;
    
    Vector<Integer> clauses[] = new Vector[2];
    int _lits_count[] = new int[2];
    
    int _2_lits_count[] = new int[2];
    
    int _scores[] = new int[2];
    
    public Variable()
    {
    	clauses[0] = new Vector<Integer>();
    	clauses[1] = new Vector<Integer>();
    	
    	_dlevel = -1;
    	_assign_stack_pos=-1;
    	enable_branch = true;
    	_marked = false;
    	_antecedent = NULL_CLAUSE;
    }

    public int score()
    {
    	int result = _scores[0]>_scores[1]?_scores[0]:_scores[1];
    	if(_dlevel==0)
    		result = -1;
    	return result;
    }

}

class CSP
{
    ArrayList<Clause> constraints;
    boolean global_status = false;
}

class Clause
{
    ArrayList<CLitPoolElement> literals;
    boolean local_status = false;
    int VarIndex[] = new int[2];
    int _activity;
    int _gflag;
    int _num_lits;
    int _status = 3;
    int _id = 29;
    int _sat_lit_idx;
    
    Vector<Integer> _first_lit;
    
     boolean gid(int i) {
        return ((_gflag & (1 << (i - 1))) != 0);
      }

      void set_gid(int i) {
        _gflag |= (1 << (i - 1));
      }

      void clear_gid(int i) {
        _gflag &= ~(1 << (i - 1));
      }
}

class CSatSolver
{
	int UNDETERMINED = 0;
	int CONFLICT = 1;
	int NO_CONFLICT = 5;
	int UNSATISFIABLE = 2;
	int SATISFIABLE = 3;
	int NO_NEXT_BRANCH = 4;
	
	int outcome = 0;
	int num_free_variables=0;
	
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

class Pair implements Comparable
{
	Variable var;
	int second;
	int first;
	
	public int compareTo(Object obj)
	{
		Pair p2 = (Pair)obj;
		return (this.second>=p2.second)?1:0;
	}
}

class ImplicationQueue
{
	Queue<CImplication> _queue = new LinkedList<CImplication>();
}

class CLAUSE_STATUS {
    static int ORIGINAL_CL=0;
    static int CONFLICT_CL=1;
    static int DELETED_CL=2;
}

class CLitPoolElement {
	  
    int _val;

  
    // constructors  destructors
    public CLitPoolElement(){
    	_val=0;        
    	}

    // member access function
    int val() {
      return _val;
    }

    // stands for signed variable, i.e. 2*var_idx + sign
    int s_var() {
      return _val >> 2;
    }

    int var_index() {
      return _val >> 3;
    }

    int var_sign() {
      return ((_val >> 2) & 0x1);
    }

    void set(int s_var) {
      _val = (s_var << 2);
    }

    void set(int vid, int sign) {
      _val = (((vid << 1) + sign) << 2);
    }

    // followings are for manipulate watched literals
    int direction() {
      return ((_val & 0x3) - 2);
    }

    boolean is_watched() {
      return ((_val & 0x3) != 0);
    }

    void unwatch() {
      _val = _val & (~0x3);
    }

    void set_watch(int dir) {
      _val = _val + dir + 2;
    }

    // following are used for spacing (e.g. indicate clause's end)
    boolean is_literal() {
      return _val > 0;
    }

    void set_clause_index(int cl_idx) {
      _val = - cl_idx;
    }

    int get_clause_index() {
      //assert(_val <= 0);
      return -_val;
    }

    // misc functions
    int find_clause_index() {
      CLitPoolElement ptr;
      for (ptr = this; ptr.is_literal();); //hack
		return ptr.get_clause_index();
    }

    
}