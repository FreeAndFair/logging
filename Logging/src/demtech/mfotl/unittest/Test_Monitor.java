package demtech.mfotl.unittest;

import java.util.Arrays;
import java.util.Collection;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import demtech.mfotl.Monitor;
import demtech.mfotl.Signature;
import demtech.mfotl.TemporalStructure;

@RunWith(value = Parameterized.class)
public class Test_Monitor {
    final private Monitor my_monitor_test;
    final private Signature test_signature = TestSetting.initializeSignature("./src/demtech/mfotl/e1.sig");
    final private TemporalStructure test_ts = TestSetting.initializeTemporalStructure("./src/demtech/mfotl/e1.log");
    
    public Test_Monitor(final String a_fs) {
        my_monitor_test = new Monitor(a_fs, test_signature);
        
        //my_monitor_test = new Monitor("E x ( in (x) ) S [0,5) out (2)", test_signature);
        //my_monitor_test = new Monitor("E x ( in (x) ) S [0,5) out (2)", test_signature);
        //my_monitor_test = new Monitor("out (4) S [0,3) (in (2))", test_signature);
        //my_monitor_test = new Monitor("N (N out (4))", test_signature);
        //my_monitor_test = new Monitor("N out (4)", test_signature);
        //my_monitor_test = new Monitor("E x (P[0,5) out (x))", test_signature);
        //my_monitor_test = new Monitor("P (P (P out (3)))", test_signature);
        //my_monitor_test = new Monitor("P out (3)", test_signature);
        //my_monitor_test = new Monitor(, test_signature);
        //my_monitor_test = new Monitor("E x y ( out (x) & in(y) )", test_signature);
        //my_monitor_test = new Monitor("E x y ( out (x) & in(3) )", test_signature);
        //my_monitor_test = new Monitor("E x y ( out (x) )", test_signature);
    }
    
    @Parameters
    public static Collection<String[]> data() {
        //final String[][] data = new String[][] {{"in ( 3 )"}, {"E x ( out (x) & in(x) )"}, {"(in (2) U [0,5) out (2)) & True"}};
        final String[][] data = new String[][] {{"True S approve(r)"}, {"publish(r) & (! (True S approve(r)))"}, {"!( E r (publish(r) & (! (True S approve(r)))))"}};
        return Arrays.asList(data);
    }
    
    @Before
    public void setUp() throws Exception {
    }

    @After
    public void tearDown() throws Exception {
    }

    @Test(timeout = 100)
    public void test() {
        for (int i = 0; i < test_ts.getSize(); i++) {
            my_monitor_test.addStructure(test_ts.getStructure(i), test_ts.getTime(i));
        }
    }
}
