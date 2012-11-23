package solver;

import java.io.BufferedReader;
import java.io.DataInputStream;
import java.io.FileInputStream;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.Vector;

public class expressionsolver {

	/**
	 * @param args
	 */
	
	public expressionsolver()
	{
		String stringAssignment = "-1 2 -3 -4 -5 6 -7 -8 -9 10 11 -12 -13 14 15 16 -17 18 19 20 -21 22 23 24 25 -26 -27 -28 -29 -30 -31 32 -33 -34 35 36 -37 -38 39 40 -41 42 43 44 -45 46 47 -48 -49 50";
		String vals[] = stringAssignment.split(" ");
		int _cVar = vals.length;
		int assignment[] = new int[_cVar];
		for(int i =0 ; i<_cVar;i++)
		{
			assignment[i]=(Integer.parseInt(vals[i])>0?1:0);
		}
		
		String filename = "C:\\Users\\user\\Documents\\NetBeansProjects\\SAT\\case\\test1cs.cnf";
		
		CSP csp = generateConstraints(filename);
		if(checkresult(csp,assignment))
		{
			System.out.println("ok");
		}
		else
		{
			System.out.println("ok");
		}
		
	}
	
	public boolean checkresult(CSP csp,int[] assignment)
	{
		for (Clause constraint : csp.constraints) {
           if((checkClauseResult(constraint, assignment)==0)) return false;
        }
		return true;
	}
	
	 public int checkClauseResult(Clause constraint , int assignment[])
	    {
	        int val = 0;
	        for(Variable cspvar:constraint.variable)
	        {
	            int key = abs(cspvar.key);
	            int value = assignment[key-1];
	            value = (cspvar.key<0)?(value+1)%2:value;
	            val|=value;
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
        csp.constraints = new ArrayList<Clause>(clauses.size());
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
	
	public static void main(String[] args) {
		// TODO Auto-generated method stub
		new expressionsolver();
	}

}

class Variable
{
    int key;
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