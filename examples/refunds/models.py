"""The data a refund rule sees. The constraints are facts the verifier relies on."""

from typing import Annotated, Literal

from pydantic import BaseModel, Field


class Order(BaseModel):
    status: Literal["delivered", "damaged", "lost"]
    days_since_delivery: Annotated[int, Field(ge=0, le=365)]
    total_cents: Annotated[int, Field(ge=0, le=1_000_000)]
