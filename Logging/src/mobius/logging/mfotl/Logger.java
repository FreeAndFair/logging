package mobius.logging.mfotl;

//TODO add specs and docs

import java.io.PrintStream;
import java.util.List;
import java.util.Set;

public class Logger {
    // Attributes
    private final PrintStream my_logger;
    private final boolean my_print_info;
    
    // Constructors
    
    public Logger() {
        my_logger = getLogger();
        my_print_info = true;
    }
    
    public Logger(final boolean a_print_info) {
        my_logger = getLogger();
        my_print_info = a_print_info;
    }
    
    // Private Method
    private PrintStream getLogger() {
        return System.out;
    }
    
    // Public Method
    public /*@ pure @*/ void debug(final String a_debug_info) {
        if (my_print_info) {
            my_logger.println("debug: " + a_debug_info);
        }
    }
    
    public /*@ pure @*/ void debug(final String[] a_debug_info) {
        if (my_print_info) {
            my_logger.print("debug: ");
            for (int i = 0; i < a_debug_info.length; i++) {
                my_logger.print(a_debug_info[i]);
            }
            my_logger.println("");
        }
    }
    
    public /*@ pure @*/ void debug(final Set a_debug_info) {
        if (my_print_info) {
            my_logger.print("debug: ");
            for (Object i: a_debug_info) {
                my_logger.print(i);
            }
            my_logger.println("");
        }
    }
    
    public /*@ pure @*/ void debug(final List a_debug_info) {
        if (my_print_info) {
            my_logger.print("debug: ");
            for (Object i: a_debug_info) {
                my_logger.print(i);
            }
            my_logger.println("");
        }
    }
    
    public /*@ pure @*/ void info(final String _info) {
        if (my_print_info) {
            my_logger.println("info: " + _info);
        }
    }
    
    /*
     * fatal information, exit after output it
     */
    public /*@ pure @*/ void fatal(final String _fatal) {
        if (my_print_info) {
            my_logger.println("fatal: " + _fatal);
            
            System.exit(0);
        }
    }
    
    /*
     * error information, exit after output it
     */
    public /*@ pure @*/ void error(final String _error) {
        if (my_print_info) {
            my_logger.println("error: " + _error);
            System.exit(1);
        }
    }
}