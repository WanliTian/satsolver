package satdpll;

import java.io.BufferedReader;
import java.io.DataInputStream;
import java.io.FileInputStream;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.Date;
import java.util.HashMap;
import java.util.Iterator;
import java.util.PriorityQueue;
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
    int SATISFIABLE = 1;
    
    int UNSATISFIABLE = 2;
    int UNSATISFIABLEuA = 3;
    
    int VariableNotInClause = 0; 
    int VariableInClause = 1;
    int VariableNegationInClause = 2;
    
    int _numberOfVariables = 0 , _numberOfClauses = 0;
    int domain[] = {1,0};
    int assignments[] ;
    int occurences[];    
    CSP csp;
    HashMap<String, Integer> collision;
    
    public sat(String filename)
    {
	    System.out.println("Min Conflicts");
	    collision = new HashMap<String,Integer>();
	    csp = generateConstraints(filename);
	    boolean sanity_check=true,result = false;
	    if(sanity_check)
	    {
	    	result = (dpll(csp.constraints)==SATISFIABLE);
	    }
	    else
	    {
	    	// sanity check is false
	    }
	//    boolean crosscheck  =; 
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
    
    
    public int dpll(ArrayList<Clause> source)
    {
    	
    	//Step 1 reduce
    	ArrayList<Clause> local = copy(source);
    	ArrayList<Clause> temp = copy(local);
    	boolean didChange = true;
    	while(didChange)
    	{
    		didChange = false;
    		for (Iterator iterator = local.iterator(); iterator.hasNext();) {
				Clause clause = (Clause) iterator.next();
				if(clause.variable.size()==0)
				{
					return UNSATISFIABLE;
				}
				else if(clause.variable.size()==1)
				{
					didChange = true;
					temp = reduce(temp,clause.variable.get(0));
					break;
				}
			}
    		
    		if(didChange) local = copy(temp);
    	}
    	// Step 2 basic check
    	if(local.size()==0) return SATISFIABLE;
    	
    	// Step 3: Branch
    	Variable variable = chooseLiteral(local);
    	if(dpll(reduce(source, variable))==SATISFIABLE) return SATISFIABLE;
    	variable.key *=-1;
    	if(dpll(reduce(source, variable))==SATISFIABLE) return SATISFIABLE;
    	return UNSATISFIABLE;
    	
    }
    
    public Variable chooseLiteral(ArrayList<Clause> source)
    {
    	Comparator<Integer> cmp = new Comparator<Integer>()
		{
		    public int compare( Integer x, Integer y )
		    {
		        return y - x;
		    }
		};
		
		PriorityQueue<Integer> weights = new PriorityQueue<Integer>(_numberOfVariables);
		int positiveCount[] = new int[_numberOfVariables];
		int negativeCount[] = new int[_numberOfVariables];
		for(int index=0; index<_numberOfVariables; index++)
		{
			positiveCount[index]=0;
			negativeCount[index]=0;
		}
		
    	for (Clause clause : source) {
			ArrayList<Variable> vars = clause.variable;
			for (Variable variable : vars) {
				int key =variable.key; 
				if(key>0)
				{
					positiveCount[abs(key)-1]+=1;
				}
				else
				{
					negativeCount[abs(key)-1]+=1;
				}
			}
		}
    	int max_weight = 0;
    	Variable max= new Variable();
    	for(int index=0; index<_numberOfVariables; index++)
		{
    		int pcount = positiveCount[index]+1;
    		int ncount = negativeCount[index]+1;
			if(max_weight<(pcount*ncount))
			{
				max_weight = pcount*ncount;
				max.key = (index+1)*((pcount>=ncount)?1:-1);
			}
		}
    	
    	return max;
    }
    
    public ArrayList<Clause> reduce(ArrayList<Clause> source,Variable variable)
    {
    	int clause_index = 0 ;
    	ArrayList<Clause> local = copy(source);
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
                        occurences = new int[_numberOfVariables];
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
    int referencedKey=-1;
    boolean checkedbothways = false;
    int positiveCount = 0;
    int negativeCount = 0;
}

class CSP
{
    ArrayList<Clause> constraints;
    boolean global_status = false;
}

class Clause
{
    ArrayList<Variable> variable;
    boolean local_status = false;
}
