
```python
import tweepy


auth = tweepy.OAuth2BearerHandler(bear)

api = tweepy.API(auth)

public_tweets = api.home_timeline()
for tweet in public_tweets:
    print(tweet.text)

```

```python
import requests
from bs4 import BeautifulSoup
import markdownify
import os

# Replace with your Twitter username
TWITTER_USERNAME = 'sandmouth'
TWITTER_URL = f"https://twitter.com/{TWITTER_USERNAME}/with_replies"

def get_retweets(url):
    """
    Get the most recent retweets from the given Twitter profile.
    """
    response = requests.get(url)
    if response.status_code != 200:
        raise Exception(f"Failed to load page with status code {response.status_code}")
    print(response.content)
    soup = BeautifulSoup(response.content, 'html.parser')
    tweets = soup.find_all('div', {'data-testid': 'tweet'})

    retweets = []
    for tweet in tweets:
        if tweet.find('div', {'data-testid': 'retweet'}):
            retweets.append(tweet)
    return retweets

def tweets_to_markdown(tweets):
    """
    Convert a list of tweets to a markdown string.
    """
    markdown_str = "# Retweets\n\n"
    for tweet in tweets:
        tweet_url = "https://twitter.com" + tweet.find('a', {'href': True})['href']
        tweet_text = tweet.find('div', {'lang': True}).text if tweet.find('div', {'lang': True}) else "No text"
        user_name = tweet.find('span', {'class': 'css-901oao'}).text if tweet.find('span', {'class': 'css-901oao'}) else "Unknown User"
        user_handle = tweet.find('span', {'class': 'css-16my406'}).text if tweet.find('span', {'class': 'css-16my406'}) else "Unknown Handle"

        markdown_str += f"### {user_name} ({user_handle})\n"
        markdown_str += f"[Link to Tweet]({tweet_url})\n\n"
        markdown_str += f"{markdownify.markdownify(tweet_text)}\n\n"
        markdown_str += "---\n\n"
    return markdown_str

def save_to_file(content, filename="retweets.md"):
    """
    Save a string to a markdown file.
    """
    with open(filename, 'w') as file:
        file.write(content)

if __name__ == "__main__":
    retweets = get_retweets(TWITTER_URL)
    markdown_content = tweets_to_markdown(retweets)
    save_to_file(markdown_content)
    print(f"Retweets saved to {os.path.abspath('retweets.md')}")


```

```python
from selenium import webdriver
from selenium.webdriver.chrome.service import Service as ChromeService
from webdriver_manager.chrome import ChromeDriverManager
from bs4 import BeautifulSoup
import markdownify
import os
import time
# Replace with your Twitter username
TWITTER_USERNAME = 'sandmouth'
TWITTER_URL = f"https://twitter.com/{TWITTER_USERNAME}/with_replies"

def get_retweets(url):
    """
    Get the most recent retweets from the given Twitter profile using Selenium.
    """
    driver = webdriver.Chrome(service=ChromeService(ChromeDriverManager().install()))
    driver.get(url)
    time.sleep(10)
    html = driver.page_source
    driver.quit()
    
    soup = BeautifulSoup(html, 'html.parser')
    tweets = soup.find_all('div', {'data-testid': 'tweet'})
    
    retweets = []
    for tweet in tweets:
        if tweet.find('div', {'data-testid': 'retweet'}):
            retweets.append(tweet)
    return retweets

def tweets_to_markdown(tweets):
    """
    Convert a list of tweets to a markdown string.
    """
    markdown_str = "# Retweets\n\n"
    for tweet in tweets:
        tweet_url = "https://twitter.com" + tweet.find('a', {'href': True})['href']
        tweet_text = tweet.find('div', {'lang': True}).text if tweet.find('div', {'lang': True}) else "No text"
        user_name = tweet.find('span', {'class': 'css-901oao'}).text if tweet.find('span', {'class': 'css-901oao'}) else "Unknown User"
        user_handle = tweet.find('span', {'class': 'css-16my406'}).text if tweet.find('span', {'class': 'css-16my406'}) else "Unknown Handle"

        markdown_str += f"### {user_name} ({user_handle})\n"
        markdown_str += f"[Link to Tweet]({tweet_url})\n\n"
        markdown_str += f"{markdownify.markdownify(tweet_text)}\n\n"
        markdown_str += "---\n\n"
    return markdown_str

def save_to_file(content, filename="retweets.md"):
    """
    Save a string to a markdown file.
    """
    with open(filename, 'w') as file:
        file.write(content)

if __name__ == "__main__":
    retweets = get_retweets(TWITTER_URL)
    markdown_content = tweets_to_markdown(retweets)
    save_to_file(markdown_content)
    print(f"Retweets saved to {os.path.abspath('retweets.md')}")

```
