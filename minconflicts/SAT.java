package minconflicts;

/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

import java.io.BufferedReader;
import java.io.DataInputStream;
import java.io.FileInputStream;
import java.io.InputStreamReader;
import java.util.Date;
import java.util.Iterator;
import java.util.Vector;

/**
 *
 * @author user
 */
public class SAT {
    
    int NO_VALUE = -1;
    
    int _numberOfVariables = 0 , _numberOfClauses = 0;
    int domain[] = {1,0};
    int assignments[] ;
    boolean hardAssignment[];
    CSP csp;
    
    public SAT(String filename)
    {
        System.out.println("Min Conflicts");
        csp = generateConstraints(filename);
        assignments = new int[_numberOfVariables];
        hardAssignment = new boolean[_numberOfVariables];
        for (int i = 0; i < _numberOfVariables; i++) {
            assignments[i] = 1; // initial assignment
            hardAssignment[i] = false;
        }
        long min_steps = _numberOfClauses+_numberOfVariables;
//        long max_steps = (long)(_numberOfVariables*Math.sqrt(_numberOfClauses));
        long max_steps = (long)(min_steps*0.16*Math.sqrt(_numberOfClauses));
        max_steps = (max_steps<min_steps?min_steps:max_steps);
        boolean sanity_check = preprocessing();
        System.out.println("Preprocessing Done.");
        boolean result = false;
        if(sanity_check)
        {
        	result = min_conflicts(max_steps);
        }
        else
        {
        	// sanity check is false
        }
        boolean crosscheck = CheckResult(assignments, null); 
        if(result && crosscheck){
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
    public void reduce(Clause clauses[],int index,int value)
    {
    	Vector v = new Vector();
    	value = (index+1)*(value==1?1:-1);
    	for (int i = 0; i < clauses.length; i++) {
			Clause clause = clauses[i];
			boolean found = false,negationFound = false;
			Vector vars = new Vector<>();
			for (int j = 0; j < clause.variable.length; j++) {
				Variable var = clause.variable[j];
				if(var.key == value)
				{
					found = true;
					break;
				}
				else if(abs(var.key)==abs(value)) {
					negationFound = true;
					continue;
				}
				vars.add(var);
			}
			
			if(found)
			{
				continue;
			}
			else
			{
				if(negationFound)
				{
					Variable var[] = new Variable[vars.size()];
					for (int j = 0; j < vars.size(); j++) {
						var[j]=(Variable)vars.get(j);
					}
					clause.variable=var;
				}
				else
				{}
				v.add(clause);
			}
		}
    	
    	clauses = new Clause[v.size()];
    	for(int innerIndex = 0 ; innerIndex<v.size();innerIndex++)
    	{
    		clauses[innerIndex] = (Clause)v.get(innerIndex);
    	}
    }
    public boolean preprocessing()
    {
        boolean secondClause = false;
        
        //optimization 1 .
        // Unit propogation assigned hard values
        // say u and another clause containing u|a . Can remove the clause u|a as u is already 1
        // can remove the clause u from the list of clauses as u can only take 1 and is already assigned
        Clause clauses[] = csp.constraints;
        for (Clause constraint : csp.constraints) {
            if(constraint.variable.length == 1 && clauses.length!=0)
            {
                int key = constraint.variable[0].key;
                int assignment = (key>0)?1:0;
                int index = abs(key)-1;
                boolean hardresult = hardAssignment[index];
                if (hardAssignment[index] && assignments[index]!=assignment) {
                	return false; // both u and ~u are present
				}
                assignments[index] = assignment ;
                hardAssignment[index]=true;
                reduce(clauses,index,assignment);
                secondClause = true;
            }
        }
        
        csp.constraints = clauses;
        _numberOfClauses = clauses.length;
        
        if(secondClause){
        for (Clause constraint : csp.constraints) {
            if(constraint.variable.length == 2)
            {
                int key1 = constraint.variable[0].key;
                int key2 = constraint.variable[1].key;
                int val1 = assignments[abs(key1)-1];
                int val2 = assignments[abs(key2)-1];
                if(hardAssignment[abs(key1)-1] && !hardAssignment[abs(key2)-1])
                {
                    assignments[abs(key2)-1] = (key2>0)?1:0;
                    hardAssignment[abs(key2)-1] = true;
                }
                else if(!hardAssignment[abs(key1)-1] && hardAssignment[abs(key2)-1])
                {
                    assignments[abs(key1)-1] = (key1>0)?1:0;
                    hardAssignment[abs(key1)-1] = true;
                }
            }
        }
        }
        return true;
    }
    
    public boolean min_conflicts(long max_steps)
    {
        // current is assignments
        int conflicts[] = new int[_numberOfVariables];
        
        for(long index=0 ; index<max_steps;index++)
        {
            initializeConflicts(conflicts);
            boolean result = CheckResult(assignments, conflicts);
            if(result==true)
            {
                return true;
             }
//            if(index%500==0) System.out.println(index);
            int key = maxconflicts(conflicts);
            int val = assignments[key] ;
            val = (val+1)%2;
            assignments[key] = val;
        }
        return false;
    }
    
    public int maxconflicts(int conflicts[])
    {
        int count = conflicts[0] ;
        Vector v = new Vector();
        for (int i = 0; i < conflicts.length; i++) {
            if(conflicts[i]!=0) {
                v.add(i);
            }
        }
        int index = (int)(Math.random()*v.size());
        return (Integer)v.get(index);
    }
    
    public void initializeConflicts(int conflicts[])
    {
        for (int i = 0; i < conflicts.length; i++) {
            conflicts[i]=0;
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
    
    public static void main(String args[])
    {
        
    }
    
}



class Variable
{
    int key;
    int currentValue=-1;
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
