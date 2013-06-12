package demtech.mfotl.testsuite;

import static org.junit.Assert.*;

import java.io.BufferedReader;
import java.io.DataInputStream;
import java.io.FileInputStream;
import java.io.InputStreamReader;
import java.util.Arrays;
import java.util.Collection;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import demtech.mfotl.AtomicFormula;
import demtech.mfotl.Predicate;
import demtech.mfotl.Signature;

@RunWith(value = Parameterized.class)
public class Test_AtomicFormula {
    private final AtomicFormula a_atomicformula;
    private final Signature my_signature = initializeSignature("./src/demtech/mfotl/e1.sig");
    
    public Test_AtomicFormula(final String a_afs) {
        a_atomicformula = new AtomicFormula(a_afs.split(" "), my_signature);
    }
    
    @Parameters
    public static Collection<String[]> data() {
        final String[][] data = new String[][] {{"out ( 5 )"}, {"in ( 3 )"}, {"True"}, {"False"}, {"True "}};
        return Arrays.asList(data);
    }
    
    @Before
    public void setUp() throws Exception {
        
    }

    @After
    public void tearDown() throws Exception {
        
    }

    //@Ignore("not ready")
    @Test
    public void test() {
        System.out.println(a_atomicformula.toString());
        //fail("Not yet implemented");
    }

    private static Signature initializeSignature(final String a_file) {
        final Signature a_signature = new Signature();
        
        try {
            final FileInputStream fstream = new FileInputStream(a_file);
            final DataInputStream in = new DataInputStream(fstream);
            final BufferedReader br = new BufferedReader(new InputStreamReader(in));
            String str_line;
            while ((str_line = br.readLine()) != null) {
                //System.out.println("Relation: " + str_line);
                String[] str_tokens = str_line.split(" ");
                int an_arity = str_tokens[1].split(",").length;
                a_signature.addPredicate(new Predicate(str_tokens[0], an_arity));
            }
            br.close();
            in.close();
            fstream.close();
        } catch (Exception e) {
            System.out.println("Current dir using System:" + System.getProperty("user.dir"));
            System.err.println("Error: " + e.getMessage());
        }

        return a_signature;
    }
}
