package mobius.logging;

import java.io.Writer;
import java.util.Date;
import java.util.Properties;

import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;
import java.text.DateFormat;
import java.text.SimpleDateFormat;

/**
 * <p> The primary class used to send debugging messages to a
 * DBMS output channel. </p>
 *
 * @version $Revision: 1.0 $ $Date: 2012/12/14 11:45:00 $
 * @author Jian Wang <jwan@itu.dk>
 * @see Context
 * @see Debug 
 */

public class DatabaseOutput  extends AbstractDebugOutputBase
implements DebugOutput, Cloneable
{   
    // private String framework = "embedded";
    private String driver = "org.apache.derby.jdbc.EmbeddedDriver";
    private String protocol = "jdbc:derby:";
    private Connection conn = null;
    private Statement s = null;
    private ResultSet rs = null;
    
    private void databaseInit()
    {
        try 
        {
            Class.forName(driver).newInstance();
            System.out.println("Loaded the appropriate driver.");
            
            Properties props = new Properties();
            props.put("user", "user1");
            props.put("password", "user1");
           
            //create=true to create idebugDB
            conn = DriverManager.getConnection(protocol +"idebugDB;create=true", props);
            System.out.println("Connected to and created database idebugDB");
            
            conn.setAutoCommit(false);// Set Auto Commit
            s = conn.createStatement();
        } catch (Exception e)
        {
            
        }
    }

    @Override
    public void printMsg(String category, String message)
    {
        try
        {
            s.execute("insert into idebugDB values (" + category + ", -1 , '" + message + "' , '" + getTime() + ")");
        }
        catch (Exception e)
        {
            
        }
    }

    @Override
    public void printMsg(int level, String message) 
    {
        try
        {
            s.execute("insert into idebugDB values (" + "'null', " + level + ", " + message + "' , '" + getTime() + ")");
        }
        catch (Exception e)
        {
            
        }
    }

    @Override
    public void printMsg(String message) 
    {
        try
        {
            s.execute("insert into idebugDB values (" + "'null', -1 ," + message + "' , '" + getTime() + ")");
        }
        catch (Exception e)
        {
            
        }
    }


    public Object clone()
    {
        try
        {
              return super.clone();
        } catch (CloneNotSupportedException cnse) 
        {
            throw new RuntimeException(cnse.getMessage());  
        }
    }
      
      // Constructors

      /**
       * <p> Constructor for <code>WriterOutput</code>. </p>
       *
       * @param d the <code>Debug</code> object associated with this
       * <code>WriterOutput</code>.
       */

      public DatabaseOutput(Debug d)
      {       
          /** require [d_non_null] (d != null); **/

          my_debug = d;

          /** ensure [debug_is_valid] (debug == d); 
            changeonly{debug}; **/
          databaseInit();
      }
      
      public void closeDatabase()
      {
          try
          {
              if (rs != null)
                  rs.close();
              if (s != null)
                  s.close();
              
              System.out.println("Closed result set and statement");
              conn.commit();
              conn.close();
              DriverManager.getConnection("jdbc:derby:idebugDB;shutdown=true");
          } catch (SQLException e)
          {
              
          }

          System.out.println("Committed transaction and closed connection");
      }
      
      private String getTime()
      {
          DateFormat dateFormat = new SimpleDateFormat("yyyy/MM/dd HH:mm:ss");
          Date date = new Date();
          return dateFormat.format(date);
      }

    @Override
    public Writer getWriter() {
        // TODO Auto-generated method stub
        return null;
    }
}