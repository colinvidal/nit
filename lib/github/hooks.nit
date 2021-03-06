# This file is part of NIT ( http://www.nitlanguage.org ).
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

# Github hook event listening with `nitcorn`.
#
# Usage:
#
# ~~~
# import github::hooks
#
# # A simple hook listener that print received events in stdout.
# class LogHookListener
#    super HookListener
#
#    # Use double dispatch to implement log behavior.
#    redef fun apply_event(event) do event.log_event(self)
# end
#
# redef class GithubEvent
#    # Log this event.
#    #
#    # Do nothing by default.
#    fun log_event(l: LogHookListener) do end
# end
#
# redef class CommitCommentEvent
#
#    redef fun log_event(l) do
#        print "new comment on commit {comment.commit.sha}"
#    end
# end
#
# var api = new GithubAPI(get_github_oauth)
# var listener = new LogHookListener(api, "127.0.0.1", 8080)
# # listener.listen # uncomment to start listening
# ~~~
module hooks

import events
import nitcorn

# A nitcorn listener for Github hooks.
class HookListener

	# Api client used to perform Github API requests.
	var api: GithubAPI

	# Host to listen.
	var host: String

	# Port to listen.
	var port: Int

	# VirtualHost listened
	private var vh: VirtualHost is noinit

	init do
		vh = new VirtualHost("{host}:{port}")
		vh.routes.add new Route("/", new HookAction(self))
	end

	# Verbosity level (0: quiet, 1: debug).
	# Default: 0
	var verbosity = 0

	# Print `message` if `lvl` <= `verbosity`
	fun message(lvl: Int, message: String) do
		if lvl <= verbosity then print message
	end

	# Start listening and responding to event.
	fun listen do
		message(1, "Hook listening on {host}:{port}")
		var factory = new HttpFactory.and_libevent
		factory.config.virtual_hosts.add vh
		factory.run
	end

	# How to build events from received json objects.
	fun event_factory(kind: String, json: JsonObject): GithubEvent do
		if kind == "commit_comment" then
			return new CommitCommentEvent.from_json(api, json)
		else if kind == "create" then
			return new CreateEvent.from_json(api, json)
		else if kind == "delete" then
			return new DeleteEvent.from_json(api, json)
		else if kind == "deployment" then
			return new DeploymentEvent.from_json(api, json)
		else if kind == "deployment_status" then
			return new DeploymentStatusEvent.from_json(api, json)
		else if kind == "fork" then
			return new ForkEvent.from_json(api, json)
		else if kind == "issues" then
			return new IssuesEvent.from_json(api, json)
		else if kind == "issue_comment" then
			return new IssueCommentEvent.from_json(api, json)
		else if kind == "member" then
			return new MemberEvent.from_json(api, json)
		else if kind == "pull_request" then
			return new PullRequestEvent.from_json(api, json)
		else if kind == "pull_request_review_comment" then
			return new PullRequestReviewCommentEvent.from_json(api, json)
		else if kind == "push" then
			return new PushEvent.from_json(api, json)
		else if kind == "status" then
			return new StatusEvent.from_json(api, json)
		else
			return new GithubEvent.from_json(api, json)
		end
	end

	# What to do when we receive an event from a hook?
	fun apply_event(event: GithubEvent) is abstract
end

# A nitcorn action dedicated to GitHub hook listening.
private class HookAction
	super Action

	# Listener that contains this action.
	#
	# The `listener` is used for its `event_factory` method
	# and the `apply_event`.
	var listener: HookListener

	# Parse hook request then call `listener.apply_event`.
	redef fun answer(request, uri) do
		# get event type
		var kind = request.header.get_or_null("X-GitHub-Event")
		if kind == null then return new HttpResponse(403)
		# get POST object
		var obj = request.body.parse_json
		if not obj isa JsonObject then return new HttpResponse(403)
		# parse event
		var event = listener.event_factory(kind, obj)
		listener.apply_event(event)
		return new HttpResponse(200)
	end
end
