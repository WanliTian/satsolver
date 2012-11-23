package template;

import java.io.BufferedReader;
import java.io.DataInputStream;
import java.io.FileInputStream;
import java.io.InputStreamReader;
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
    
    int _numberOfVariables = 0 , _numberOfClauses = 0;
    int domain[] = {1,0};
    int assignments[] ;
    int occurences[];
    boolean hardAssignment[];
    CSP csp;
    HashMap<String, Integer> collision;
    public sat(String filename)
    {
	    System.out.println("Min Conflicts");
	    collision = new HashMap<String,Integer>();
	    csp = generateConstraints(filename);
	    boolean sanity_check=true,result = false;
//	    sanity_check = preprocessing();
	    long min_steps = _numberOfClauses+_numberOfVariables;
	//    long max_steps = (long)(_numberOfVariables*Math.sqrt(_numberOfClauses));
	//    long max_steps = (long)(min_steps*0.16*Math.sqrt(_numberOfClauses));
	    long max_steps = (long)(min_steps*min_steps*2);
	    System.out.println(_numberOfVariables+" "+_numberOfClauses+" "+max_steps);
	    max_steps = (max_steps<min_steps?min_steps:max_steps);
	    System.out.println("Preprocessing Done.");
	    
	    if(sanity_check)
	    {
//	    	result = min_conflicts(max_steps);
	    }
	    else
	    {
	    	// sanity check is false
	    }
	//    boolean crosscheck  =; 
	    if(result &&  CheckResult(assignments, null)){
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
        Vector possibleConflicts = new Vector(constraint.variable.length);        
        for(Variable cspvar:constraint.variable)
        {
            int key = abs(cspvar.key);
            int value = assignment[key-1];
            value = (cspvar.key<0)?(value+1)%2:value;
            val|=value;
            if(!hardAssignment[key-1]) possibleConflicts.add(key);
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
        csp.constraints = new Clause[clauses.size()];
        int clause_index = 0;
        for (Iterator<String> it = clauses.iterator(); it.hasNext();) {
            String string = it.next();
            String split[] = string.split(" ");
            Clause clause = new Clause();
            clause.variable = new Variable[split.length-1]; // last 0 is not counted
            int variable_index = 0 ;
            for (String string1 : split) {
                int value = Integer.parseInt(string1);
                if(value==0) break;
                Variable var = new Variable();
                var.key = value;
                clause.variable[variable_index] = var;
                variable_index++;
            }
           csp.constraints[clause_index] = clause;
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
                        hardAssignment = new boolean[_numberOfVariables];
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
}

class CSP
{
    Clause constraints[];
    boolean global_status = false;
}

class Clause
{
    Variable variable[];
    boolean local_status = false;
}
