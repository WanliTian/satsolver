package satdpllmod;

import java.io.BufferedReader;
import java.io.DataInputStream;
import java.io.FileInputStream;
import java.io.InputStreamReader;
import java.security.AllPermission;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.Date;
import java.util.HashMap;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.PriorityQueue;
import java.util.Vector;

import org.omg.CosNaming.IstringHelper;


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
    int UNDEFINED = 3;
    
    int VariableNotInClause = 0; 
    int VariableInClause = 1;
    int VariableNegationInClause = 2;
    
    int _numberOfVariables = 0 , _numberOfClauses = 0;
    int domain[] = {1,0};
    int assignments[] ;
    CSP csp;
    HashMap<String, Integer> collision;
    
    public sat(String filename)
    {
	    System.out.println("DPLL");
	    collision = new HashMap<String,Integer>();
	    csp = generateConstraints(filename);
	    MAX_WEIGHT = _numberOfClauses*_numberOfVariables;
	    boolean sanity_check=true,result = false;
	    initial_assignment();
    	result = dpll(csp.constraints);
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
    
    public void initial_assignment()
    {
    	for (int i = 0; i < assignments.length; i++) {
			assignments[i]=NO_VALUE;
		}
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
        for(Variable cspvar:constraint.variable)
        {
            int key = abs(cspvar.key);
            int value = assignment[key-1];
            value = (cspvar.key<0)?(value+1)%2:value;
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
    
    public void setLocalStatus(Model m)
    {
    	ArrayList<Clause> clauses = csp.constraints;
    	for (int i = 0; i < clauses.size(); i++) {
			Clause clause = clauses.get(i);
			int status = isClauseTrueInModel(clause, m.assignments);
			clause.local_status = status;
			csp.constraints.set(i, clause);
		}
    }
    
    public boolean areAllClauseTrue(Model m)
    {
    	setLocalStatus(m);
    	ArrayList<Clause> clauses = csp.constraints;
    	for (Clause clause : clauses) {
			if(clause.local_status==UNSATISFIABLE || clause.local_status==UNDEFINED)
			{
				return false;
			}
		}
    	return true;
    }
    
    public boolean isEvenOneClauseFalse(Model m)
    {
    	setLocalStatus(m);
    	ArrayList<Clause> clauses = csp.constraints;
    	for (Clause clause : clauses) {
			if(clause.local_status==UNSATISFIABLE)
			{
				return true;
			}
		}
    	return false;
    }
    
    public SymbolValuePair findPureSymbolPair(ArrayList<Clause> source,ArrayList<Integer> variables,Model m)
    {
    	SymbolValuePair svp = null;
    	int posCount[] = new int[_numberOfVariables];
    	int negCount[] = new int[_numberOfVariables];
    	HashMap<Integer, SymbolValuePair> map = new HashMap<Integer,SymbolValuePair>();
    	for (int i = 0; i < source.size(); i++) {
			Clause clause = source.get(i);
			if(isClauseTrueInModel(clause, m.assignments)==SATISFIABLE) continue;
			for (int j = 0; j < clause.variable.size(); j++) {
				int key = clause.variable.get(j).key;
				int skey = abs(key)-1;
				posCount[skey]+=(key>0)?1:0;
				negCount[skey]+=(key<0)?1:0;
				SymbolValuePair tsvp = new SymbolValuePair();
				tsvp.key = (skey+1);
				tsvp.value = (posCount[skey]>0)?1:0;
				if(!variables.contains(new Integer(skey)) || m.assignments[skey]!=NO_VALUE) continue;
				if((posCount[skey]==0 && negCount[skey]!=0) ||
					(posCount[skey]!=0 && negCount[skey]==0) )
				{
					if(!map.containsKey(skey)) map.put(skey, tsvp);
				}
				else if(map.containsKey(skey))
				{
					map.remove(skey);
				}
			}
		}
    	
    	if(map.size()>0) svp = map.values().iterator().next();
    	return svp;
    }
    
    public SymbolValuePair findUnitSymbolPair(ArrayList<Clause> source,ArrayList<Integer> variables,Model m)
    {
    	SymbolValuePair svp=null;
    	int posCount[] = new int[_numberOfVariables];
    	int negCount[] = new int[_numberOfVariables];
    	int index=NO_VALUE;
    	for (int i = 0; i < source.size(); i++) {
			Clause clause =	source.get(i);
			if(clause.variable.size()!=1 || (isClauseTrueInModel(clause, m.assignments)!=UNDEFINED)) continue;
			int key = clause.variable.get(0).key;
			int skey = abs(key)-1;
//			if(m.assignments[skey]!=NO_VALUE || !variables.contains(new Integer(skey))) continue;
			svp = new SymbolValuePair();
			svp.key = abs(key);
			svp.value = (key>0)?1:0;
			return svp;
		}
    	
    	
    	// Type 2 - Unit propogation where all except the current variable is set and all else is false
    	for (int i = 0; i < source.size(); i++) {
			Clause clause =	source.get(i);
			if(clause.variable.size()==1) continue;
			if(isClauseTrueInModel(clause, m.assignments)!=UNDEFINED)
			{
				continue;
			}
			else
			{
				int count=0,var_index=0;
				for(int ind=0;ind<clause.variable.size();ind++)
				{
					int key = clause.variable.get(ind).key;
					int skey = abs(key)-1;
					if(m.assignments[skey]==NO_VALUE)
					{
						count++;
						var_index=ind;
					}
				}
				if(count!=1) continue;
				int key = clause.variable.get(var_index).key;
				int skey = abs(key)-1;
//				if(m.assignments[skey]!=NO_VALUE || !variables.contains(new Integer(skey))) continue;
				svp = new SymbolValuePair();
				svp.key = abs(key);
				svp.value = (key>0)?1:0;
				return svp;
			}
		}
    	return svp;
    	
    }
    
    public int isClauseTrueInModel(Clause clause,int assignments[])
    {
    	int val=0;
    	for (Variable var : clause.variable) {
    		int key = abs(var.key);
    		int value = (assignments[key-1]==1)?1:-1;
			if(assignments[key-1]==NO_VALUE)
			{
				clause.local_status=UNDEFINED;
				return clause.local_status;
			}else if(var.key!=(value*key))
			{
				val|=0;
			}
			else
			{
				val|=1;
			}
		}
    	clause.local_status=(val==1)?SATISFIABLE:UNSATISFIABLE;
    	return clause.local_status;
    }
    
    public boolean dpll(ArrayList<Clause> source)
    {
    	Model m = new Model(_numberOfVariables);
    	ArrayList<Integer> vars = new ArrayList<Integer>(_numberOfVariables);
    	for (int i = 0; i < _numberOfVariables; i++) {
			vars.add(new Integer(i));
		}
    	return (dpll(source, m,vars) == SATISFIABLE);
    }
    
    public int dpll(ArrayList<Clause> source,Model m,ArrayList<Integer> vars)
    {
    	
    	//Step 1 reduce
    	ArrayList<Clause> local = copy(source);
    	
    	if (areAllClauseTrue(m)) {
    		assignments = m.assignments;
			return SATISFIABLE;
		}
    	
    	if(isEvenOneClauseFalse(m))
    	{
    		return UNSATISFIABLE;
    	}
    	
    	SymbolValuePair svp = findPureSymbolPair(local,vars,m);
    	if(svp!=null)
    	{
    		ArrayList<Integer> var = copyVariables(vars);
    		var.remove(new Integer(svp.key-1));
    		ArrayList<Clause> temp = copy(local);
    		Model newmodel = m.extend(svp.key,svp.value);
    		return dpll(temp,newmodel,var);
    	}
    	
    	svp = findUnitSymbolPair(local,vars,m);
    	
    	if(svp!=null)
    	{
    		ArrayList<Clause> temp = copy(local);
    		ArrayList<Integer> var = copyVariables(vars);
    		var.remove(new Integer(svp.key-1));
    		Model newmodel = m.extend(svp.key,svp.value);
    		return dpll(temp,newmodel,var);
    	}
    	
    	Integer v = vars.get(0);
    	ArrayList<Integer> newvar = copyVariables(vars);
    	newvar.remove(0);
    	if((dpll(source, m.extend(v+1, 1),newvar) == SATISFIABLE) )
    	{
    		assignments = m.assignments;
    		return SATISFIABLE;
    	}
    	else if(dpll(source, m.extend(v+1, 0),newvar) == SATISFIABLE )
    	{
    		assignments = m.assignments;
    		return SATISFIABLE;
    	}
    	else
    	{
    		return UNSATISFIABLE;
    	}
    			
    	
    }
    
    public ArrayList<Integer> copyVariables(ArrayList<Integer> variables)
    {
    	ArrayList<Integer> newvar = new ArrayList<Integer>(variables.size());
    	for (Integer variable : variables) {
			newvar.add(variable);
		}
    	return newvar;
    }
    
    public void assignVariable(Variable variable)
    {
    	assignments[abs(variable.key)-1]=(variable.key>0?1:0);
    }
    public void d(String temp)
    {
    	System.out.println(temp);
    }
    
    public ArrayList<Variable> getVariablesinCSP(ArrayList<Clause> source)
    {
    	ArrayList<Variable> variables = new ArrayList<Variable>();
    	HashMap<Integer, Integer> map = new HashMap<Integer,Integer>();
    	for (Clause clause : source) {
			for (Variable variable : clause.variable) {
				if(map.containsKey(abs(variable.key)))
				{
					continue;
				}
				else
				{
					map.put(abs(variable.key), abs(variable.key));
					variables.add(variable);
				}
			}
		}
    	return variables;
    }
    
    public ArrayList<Variable> getVariablesInClause(Clause clause)
    {
    	ArrayList<Variable> vars = new ArrayList<Variable>();
    	for (Variable variable : clause.variable) {
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
			Variable var = clause.variable.get(i);
			if(var.key==variable.key) return VariableInClause;
			else if(var.key==-variable.key) return VariableNegationInClause;
		}
    	return VariableNotInClause;
    	
    }
    
    public Clause removeVariableFromClause(Clause source,Variable variable)
    {
    	for (int i = 0; i < source.variable.size(); i++) {
			Variable var = source.variable.get(i);
			if(abs(var.key)==(abs(variable.key)))
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
    
//    public Clause[] copy(Clause source[])
//    {
//    	
//    }
    
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
            clause.local_status  = UNDEFINED;
            clause.variable = new ArrayList<Variable>(split.length-1); // last 0 is not counted
            int variable_index = 0 ;
            for (String string1 : split) {
                int value = Integer.parseInt(string1);
                if(value==0) break;
                Variable var = new Variable();
                var.key = value;
//                clause.variable.set(variable_index,var);
                clause.variable.add(var);
                variable_index++;
            }
           csp.constraints.add(clause);
           clause_index++;
        }
        return csp;
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
                        assignments = new int[_numberOfVariables];
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
		// TODO Auto-generated method stub

	}

}

class Variable
{
    int key;
}

class CSP
{
    ArrayList<Clause> constraints;
     int global_status = 3;
}

class Clause
{
    ArrayList<Variable> variable;
     int local_status = 3;
}

class Model
{
	int assignments[];
	int numberOfVariables;//numberOfVariables
	
	public Model(int num)
	{
		assignments= new int[num];
		numberOfVariables = num;
		initial_assignment();
	}
	public void initial_assignment()
    {
    	for (int i = 0; i < numberOfVariables; i++) {
			assignments[i]=-1;
		}
    }
	
	public Model extend(int key,int assignment)
	{
		Model M = new Model(numberOfVariables);
		for (int i = 0; i < numberOfVariables; i++) {
			M.assignments[i]= this.assignments[i];
		}
		M.assignments[key-1]=assignment;
		return M;
	}
}

class SymbolValuePair
{
	int key;
	int value;
}