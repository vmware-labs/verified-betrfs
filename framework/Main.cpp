#include "Application.h"

int main()
{
  Mkfs();
  cout << "Mkfs done" << endl;

  Application app;
  app.Insert("abc", "def");
  app.Insert("xyq", "rawr");
  app.Query("abc");

  app.Query("xyq");
  app.Query("blahblah");
  app.crash();
  app.Query("abc");
  app.Query("xyq");

  app.Insert("abc", "def");
  app.Insert("xyq", "rawr");
  app.Insert("blahblah", "moomoo");
  app.Sync();
  app.crash();
  app.Query("abc");
  app.Query("xyq");
}
