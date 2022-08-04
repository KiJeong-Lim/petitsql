# Petit Sql
- A little model for the absence of SQL injections, namely SQL injection-free
- The SQL injection-free property
  - For all SQL expressions sql, when a string v is substitued for a variable x in sql, the structure of the SQL expression (sql) is preserved in the substituted SQL expression (injection x v sql). 
  - The property can be written in Haskell QuickCheck as follows. 
    
```
         injFree (norm sql) . norm . sqlFrom . parseSQL . printSQL . injection x v $ sql
```

## How to install and run
- [Install the Haskell tool, stack ](https://docs.haskellstack.org/en/stable/install_and_upgrade/)
- Run it:
```
   $ git clone https://github.com/kwanghoon/petitsql
   $ cd petitsql
   $ stack test

   $ stack test
   petitsql> test (suite: petitsql-test)


   SQL injection free?
     For all sql, x, and v, sql is injection-free from injection x v sql
    +++ OK, passed 100 tests.

   Finished in 0.0216 seconds
   1 example, 0 failures

   petitsql> Test suite petitsql-test passed
```
