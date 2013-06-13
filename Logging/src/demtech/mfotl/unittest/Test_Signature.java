package demtech.mfotl.unittest;

import static org.junit.Assert.*;

import java.io.BufferedReader;
import java.io.DataInputStream;
import java.io.FileInputStream;
import java.io.InputStreamReader;
import java.util.HashSet;
import java.util.Set;

import org.junit.Test;

import demtech.mfotl.Predicate;
import demtech.mfotl.Signature;

public class Test_Signature {
    private final Signature my_signature;
    private final Set<Predicate> my_pred_set;
    
    public Test_Signature() {
        my_signature = new Signature();
        my_pred_set = new HashSet<Predicate>();
        
        try {
            FileInputStream fstream = new FileInputStream("./src/demtech/mfotl/e1.sig");
            DataInputStream in = new DataInputStream(fstream);
            BufferedReader br = new BufferedReader(new InputStreamReader(in));
            String str_line;
            while ((str_line = br.readLine()) != null) {
                System.out.println("Relation: " + str_line);
                String[] str_tokens = str_line.split(" ");
                int an_arity = str_tokens[1].split(",").length;
                final Predicate tmp = new Predicate(str_tokens[0], an_arity);
                my_pred_set.add(tmp);
                my_signature.addPredicate(tmp);
            }
            br.close();
            in.close();
            fstream.close();
        } catch (Exception e) {
            System.out.println("Current dir using System:" + System.getProperty("user.dir"));
            System.err.println("Error: " + e.getMessage());
        }
    }
    
    @Test
    public void test() {
        for (Predicate p_i : my_pred_set) {
            assertTrue(my_signature.contains(p_i));
            assertTrue(my_signature.contains(p_i.getName(), p_i.getArity()));
        }
    }
}
